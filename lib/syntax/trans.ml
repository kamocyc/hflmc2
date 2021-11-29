open Hflmc2_util
open Type
module S = struct
  module Id      = Id
  module Type    = Type
  module Arith   = Arith
  module Formula = Formula
  module Hfl     = Hfl
  module Hflz    = Hflz
end

let log_src = Logs.Src.create ~doc:"Transform" "Trans"
module Log = (val Logs.src_log log_src)


module Subst = struct
  type 'x env = 'x IdMap.t
  module Id = struct
    let rec arith : [`Int ] S.Id.t env -> S.Arith.t -> S.Arith.t =
      fun env a ->
        match a with
        | Int _ -> a
        | Var v ->
            begin match IdMap.find env v with
            | None -> a
            | Some v' -> Var v'
            end
        | Op(op, as') -> Op(op, List.map ~f:(arith env) as')

    let rec formula : [`Int ] S.Id.t IdMap.t -> S.Formula.t -> S.Formula.t =
      fun env p ->
        match p with
        | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith env))
        | And ps -> And(List.map ~f:(formula env) ps)
        | Or  ps -> Or (List.map ~f:(formula env) ps)
        | _ -> p

    let rec abstraction_ty
              : [`Int ] S.Id.t env
             -> abstraction_ty
             -> abstraction_ty =
      fun env ty -> match ty with
        | TyBool fs -> TyBool (List.map fs ~f:(formula env))
        | TyArrow({ty=TyInt;_} as x, ty) ->
            TyArrow(x, abstraction_ty (IdMap.remove env x) ty)
        | TyArrow({ty=TySigma ty_arg;_} as y, ret_ty) ->
            TyArrow({y with ty = TySigma (abstraction_ty env ty_arg)},
                    abstraction_ty env ret_ty)
  end

  (* TODO IdMapを使う *)
  module Arith = struct
    let rec arith_
              : ('var -> 'var -> bool)
             -> 'var
             -> 'var S.Arith.gen_t
             -> 'var S.Arith.gen_t
             -> 'var S.Arith.gen_t =
      fun equal x a a' ->
        match a' with
        | Int _ -> a'
        | Var x' -> if equal x x' then a else a'
        | Op(op, as') -> Op(op, List.map ~f:(arith_ equal x a) as')
    let arith : 'a. 'a S.Id.t -> S.Arith.t -> S.Arith.t -> S.Arith.t =
      fun x a a' -> arith_ S.Id.eq {x with ty=`Int} a a'

    let rec formula_
              : ('var -> 'var -> bool)
             -> 'var
             -> 'var S.Arith.gen_t
             -> ('bvar,'var) S.Formula.gen_t
             -> ('bvar,'var) S.Formula.gen_t =
      fun equal x a p ->
        match p with
        | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith_ equal x a))
        | And ps -> And(List.map ~f:(formula_ equal x a) ps)
        | Or  ps -> Or (List.map ~f:(formula_ equal x a) ps)
        | _ -> p
    let formula : 'a. 'a S.Id.t -> S.Arith.t -> S.Formula.t -> S.Formula.t =
      fun x a p -> formula_ S.Id.eq {x with ty = `Int} a p

    let rec abstraction_ty
              : unit S.Id.t
             -> S.Arith.t
             -> abstraction_ty
             -> abstraction_ty =
      fun x a sigma ->
        match sigma with
        | TyBool preds ->
            TyBool (List.map ~f:(formula x a) preds)
        | TyArrow (arg,ret) ->
            TyArrow( { arg with ty = abstraction_argty x a arg.ty }
                   , abstraction_ty x a ret)
    and abstraction_argty
          : unit S.Id.t
         -> S.Arith.t
         -> abstraction_ty arg
         -> abstraction_ty arg =
      fun x a arg ->
        match arg with
        | TyInt -> TyInt
        | TySigma(sigma) -> TySigma(abstraction_ty x a sigma)
    let abstraction_ty
          : 'a S.Id.t
         -> S.Arith.t
         -> abstraction_ty
         -> abstraction_ty =
      fun x a sigma -> abstraction_ty (S.Id.remove_ty x) a sigma
    let abstraction_argty
          : 'a S.Id.t
         -> S.Arith.t
         -> abstraction_ty arg
         -> abstraction_ty arg =
      fun x a arg -> abstraction_argty (S.Id.remove_ty x) a arg
  end

  module Hflz = struct

    let rec arith : 'ty S.Hflz.t env -> S.Arith.t -> S.Arith.t =
      fun env a -> match a with
        | Int _ -> a
        | Var x ->
            begin match IdMap.find env x with
            | None -> a
            | Some (Arith a') -> a'
            | _ -> assert false
            end
        | Op(op, as') -> Op(op, List.map ~f:(arith env) as')
    
    let rec rename_bindings (phi : 'ty S.Hflz.t): 'ty S.Hflz.t =
      let rec go rename (phi : 'ty S.Hflz.t): 'ty S.Hflz.t = match phi with
        | Var x -> begin
          match IdMap.find rename x with
          | Some v -> begin
            let ty =
              (match v.S.Id.ty with
              | TySigma ty -> ty
              | TyInt -> assert false) in
            Var {v with ty}
          end
          | None -> Var x
        end
        | Or (phi1, phi2) ->
          Or (go rename phi1, go rename phi2)
        | And (phi1, phi2) ->
          And (go rename phi1, go rename phi2)
        | App (phi1, phi2) ->
          App (go rename phi1, go rename phi2)
        | Abs (x_, t) ->
          let x = { x_ with id = S.Id.gen_id () } in
          Abs (x, go (IdMap.add rename x_ x) t)
        | Forall (x_, t) ->
          let x = { x_ with id = S.Id.gen_id () } in
          Forall (x, go (IdMap.add rename x_ x) t)
        | Bool b -> Bool b
        | Arith _ | Pred _ ->
          let rename =
            IdMap.filter_map
              rename
              ~f:(fun a ->
                match a.S.Id.ty with
                | TyInt -> Some (S.Hflz.Arith (S.Arith.Var ({a with ty=`Int})))
                | TySigma _ -> None
              ) in
          hflz rename phi in
      go IdMap.empty phi
    and hflz : 'ty S.Hflz.t env -> 'ty S.Hflz.t -> 'ty S.Hflz.t =
      fun env_ phi ->
        let rec hflz_ s_env b_env (phi : 'ty S.Hflz.t): 'ty S.Hflz.t = match phi with
          | Var x ->
              begin match IdMap.lookup s_env x with
              | t -> rename_bindings t
              | exception Core.Not_found_s _ -> Var x
              end
          | Or(phi1,phi2)  ->
            Or(hflz_ s_env b_env phi1, hflz_ s_env b_env phi2)
          | And(phi1,phi2) ->
            And(hflz_ s_env b_env phi1, hflz_ s_env b_env phi2)
          | App(phi1,phi2) ->
            App(hflz_ s_env b_env phi1, hflz_ s_env b_env phi2)
          | Abs(x, t)      ->
            Abs(x, hflz_ (IdMap.remove s_env x) (IdSet.add b_env x) t)
          | Forall(x, t)   ->
            Forall(x, hflz_ (IdMap.remove s_env x) (IdSet.add b_env x) t)
          | Arith a        ->
            Arith (arith s_env a)
          | Pred (p,as')   ->
            Pred(p, List.map ~f:(arith s_env) as')
          | Bool _         -> phi
        in
        hflz_ env_ IdSet.empty phi
  end

  module Hfl = struct
    let rec hfl : S.Hfl.t env -> S.Hfl.t -> S.Hfl.t =
      fun env phi -> match phi with
        | Var x ->
            begin match IdMap.lookup env x with
            | t -> t
            | exception Core.Not_found_s _ -> Var x
            end
        | Bool _         -> phi
        | Or(phis,k)     -> Or(List.map ~f:(hfl env) phis, k)
        | And(phis,k)    -> And(List.map ~f:(hfl env) phis, k)
        | App(phi1,phi2) -> App(hfl env phi1, hfl env phi2)
        | Abs(x, t)      -> Abs(x, hfl (IdMap.remove env x) t)
  end
end

module Reduce = struct
  module Hfl = struct
    let rec beta : S.Hfl.t -> S.Hfl.t = function
      | Or (phis, k) -> Or (List.map ~f:beta phis, k)
      | And(phis, k) -> And(List.map ~f:beta phis, k)
      | App(phi1, phi2) ->
          begin match beta phi1, beta phi2 with
          | Abs(x, phi1), phi2 -> Subst.Hfl.hfl (IdMap.of_list [x,phi2]) phi1
          | phi1, phi2 -> App(phi1, phi2)
          end
      | Abs(x, phi) -> Abs(x, beta phi)
      | phi -> phi
    let rec eta : S.Hfl.t -> S.Hfl.t = function (* The Coercion rule generates many eta reduxes *)
      | Abs(x, (App (phi, Var x')))
          when Id.eq x x' && not (IdSet.mem (Hfl.fvs phi) x) -> phi
      | Abs(x, phi)     -> Abs(x, eta phi)
      | Or (phis, k)    -> Or (List.map ~f:eta phis, k)
      | And(phis, k)    -> And(List.map ~f:eta phis, k)
      | App(phi1, phi2) -> App(eta phi1, eta phi2)
      | phi             -> phi
    let beta_eta = eta <<< beta
  end
  module Hflz = struct
    let rec beta : 'a S.Hflz.t -> 'a S.Hflz.t = function
      | Or (phi1, phi2) -> Or (beta phi1, beta phi2)
      | And(phi1, phi2) -> And(beta phi1, beta phi2)
      | App(phi1, phi2) ->
          begin match beta phi1, beta phi2 with
          | Abs(x, phi1), phi2 -> beta @@ Subst.Hflz.hflz (IdMap.of_list [x,phi2]) phi1
          | phi1, phi2 -> App(phi1, phi2)
          end
      | Abs(x, phi) -> Abs(x, beta phi)
      | phi -> phi
    let rec ones = 1 :: ones
    module Scc(Key: Map.Key) = struct
      module Set = Set.Make'(Key)
      module Map = Map.Make'(Key)
      type graph = Set.t Map.t
      let rg : graph -> graph = fun g ->
        Map.fold g ~init:Map.empty ~f:begin fun ~key ~data:set map ->
          let map' =
            if Map.mem map key
            then map
            else Map.add_exn map ~key ~data:Set.empty
          in
          Set.fold set ~init:map' ~f:begin fun map v ->
            let data =
              match Map.find map v with
              | Some s -> Set.add s key
              | None   -> Set.singleton key
            in
            Map.replace map ~key:v ~data
          end
        end
      let rec dfs : graph -> Set.t -> Key.t list -> graph * Key.t list =
        fun g ls r ->
          Set.fold ls ~init:(g,r) ~f:begin fun (g,r) x ->
            match Map.find g x with
            | None -> g, r
            | Some s ->
                let g3, r3 = dfs (Map.remove g x) (Set.remove s x) r in
                g3, x::r3
          end
      let rec rdfs : graph -> Key.t -> Key.t list -> graph * Key.t list =
        fun g v ls ->
          match Map.find g v with
          | None   -> g, ls
          | Some s ->
              Set.fold s ~init:(Map.remove g v, v :: ls) ~f:begin fun (rg,ls) v ->
                rdfs rg v ls
              end
      let scc g =
        let rG = rg g in
        let map, vs = dfs g (Set.of_list @@ Map.keys g) [] in
        let _, ls =
          List.fold vs ~init:(rG, []) ~f:begin fun (rg,ls) v ->
            let rg2, l = rdfs rg v [] in
            if l == []
            then rg2, ls
            else rg2, l::ls
          end
        in
        ls
    end
    let inline : simple_ty S.Hflz.hes -> simple_ty S.Hflz.hes =
      fun rules ->
        let main, rules = match rules with
          | [] -> assert false
          | main::rules -> main, rules
        in
        let module Scc = Scc(Id.Key) in
        let dep_graph : Scc.graph =
          IdMap.of_alist_exn @@ List.map (main::rules) ~f:begin fun rule ->
            let id = rule.var in
            let dep =
              Hflz.fvs rule.body
              |> IdSet.filter ~f:begin fun x -> (* filter nonterminals *)
                  Id.is_pred_name x.Id.name (* XXX ad hoc ? *)
                 end
            in Id.remove_ty id ,dep
          end
        in
        let mutual_recursives =
          Scc.scc dep_graph
          |> List.filter ~f:(fun x -> List.length x > 1)
          |> List.concat
          |> IdSet.of_list
        in
        let rules, inlinables =
          List.partition_tf rules ~f:begin fun rule ->
            IdSet.mem mutual_recursives rule.var ||
            IdSet.mem (Hflz.fvs rule.body) rule.var ||
            Id.eq rule.var main.var
          end
        in
        let inlinables = (* topologically sort *)
          let topological_ord =
            Scc.rdfs dep_graph (Id.remove_ty main.var) []
            |> snd
            |> List.rev
            |> List.enumurate
            |> IdMap.of_alist_exn
          in
          List.sort inlinables ~compare:begin fun x y ->
            let value (z : 'a Hflz.hes_rule) =
              (* Not found when [z] is unused non-terminal *)
              Option.value ~default:0 @@ IdMap.find topological_ord z.var
            in
            Int.compare (value x) (value y)
          end
        in
        Log.info begin fun m -> m ~header:"Inline" "%a"
          Print.(list_comma id) (List.map inlinables ~f:(fun x -> x.var))
        end;
        let inline_map =
          let rules_in_map =
            IdMap.of_alist_exn @@ List.map inlinables ~f:begin fun rule ->
              Id.remove_ty rule.var, rule.body
            end
          in
          List.fold_left inlinables ~init:rules_in_map ~f:begin fun map rule ->
            let var  = rule.var in
            let body = IdMap.lookup map var in
            let map = IdMap.map map ~f:(Subst.Hflz.hflz (IdMap.singleton var body)) in
            Log.debug begin fun m ->
              let pp ppf (x,psi) = Print.(pf ppf "    %a = %a" id x (hflz simple_ty_) psi) in
              m ~header:"Inline" "%a inlined:@.@[<v>%a@]"
                Print.id rule.var
                Print.(list pp) (IdMap.to_alist map)
            end;
            map
          end
        in
        List.map (main::rules) ~f:begin fun rule ->
          { rule with body = Subst.Hflz.hflz inline_map rule.body }
        end
  end
end

module Simplify = struct
  let hflz : 'a Hflz.t -> 'a Hflz.t =
    let rec is_trivially_true : 'a Hflz.t -> bool =
      fun phi -> match phi with
      | Bool b -> b
      | Or (phi1,phi2) -> is_trivially_true phi1 || is_trivially_true phi2
      | And(phi1,phi2) -> is_trivially_true phi1 && is_trivially_true phi2
      | _ -> false
    in
    let rec is_trivially_false : 'a Hflz.t -> bool =
      fun phi -> match phi with
      | Bool b -> not b
      | And(phi1,phi2) -> is_trivially_false phi1 || is_trivially_false phi2
      | Or (phi1,phi2) -> is_trivially_false phi1 && is_trivially_false phi2
      | _ -> false
    in
    let rec go phi =
      match Reduce.Hflz.beta phi with
      | And(phi1, phi2) ->
          let phi1 = go phi1 in
          let phi2 = go phi2 in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_true) [phi1;phi2] in
          Hflz.mk_ands phis
      | Or (phi1, phi2) ->
          let phi1 = go phi1 in
          let phi2 = go phi2 in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_false) [phi1;phi2] in
          Hflz.mk_ors phis
      | Abs(x, phi)     -> Abs(x, go phi)
      | App(phi1, phi2) -> App(go phi1, go phi2)
      | Forall(x, phi)  -> Forall(x, go phi)
      | phi -> phi
    in go
  let hflz_hes_rule : 'a Hflz.hes_rule -> 'a Hflz.hes_rule =
    fun rule -> { rule with body = hflz rule.body }
  let hflz_hes : simple_ty Hflz.hes -> simple_ty Hflz.hes =
    fun rules ->
      rules
      |> begin
          if !Hflmc2_options.Preprocess.inlining
          then Reduce.Hflz.inline
          else Fn.id
         end
      |> List.map ~f:hflz_hes_rule

  let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
    let is_trivially_true : Hfl.t -> bool =
      fun phi -> match phi with
      | Bool b -> b
      | _ -> false
    in
    let is_trivially_false : Hfl.t -> bool =
      fun phi -> match phi with
      | Bool b -> not b
      | _ -> false
    in
    fun ?(force=false) phi ->
      match Reduce.Hfl.beta_eta phi with
      | And(phis, k) when k = `Inserted || force ->
          let phis = List.map ~f:hfl phis in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_true) phis in
          Hfl.mk_ands phis ~kind:k
      | Or(phis, k) when k = `Inserted || force ->
          let phis = List.map ~f:hfl phis in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_false) phis in
          Hfl.mk_ors phis ~kind:k
      | And(phis, k) -> And(List.map ~f:hfl phis, k)(* preserve the structure *)
      | Or (phis, k) -> Or (List.map ~f:hfl phis, k)(* preserve the structure *)
      | Abs(x,phi)     -> Abs(x, hfl ~force phi)
      | App(phi1,phi2) -> App(hfl ~force phi1, hfl ~force phi2)
      | phi -> phi

  let rec is_true_def =
    fun phi -> match phi with
    | Formula.Bool b -> b
    | Formula.And phis -> List.for_all ~f:is_true_def phis
    | Formula.Or  phis -> List.exists  ~f:is_true_def phis
    | _ -> false
  let rec is_false_def =
    fun phi -> match phi with
    | Formula.Bool b -> not b
    | Formula.And phis -> List.exists  ~f:is_false_def phis
    | Formula.Or  phis -> List.for_all ~f:is_false_def phis
    | _ -> false

  let rec formula
            : 'bvar 'avar
            . ?is_true:(('bvar, 'avar) Formula.gen_t -> bool)
           -> ?is_false:(('bvar, 'avar) Formula.gen_t -> bool)
           -> ('bvar, 'avar) Formula.gen_t
           -> ('bvar, 'avar) Formula.gen_t =
    fun ?(is_true=is_true_def) ?(is_false=is_false_def) -> function
    | Formula.And phis ->
        let phis = List.map ~f:formula phis in
        let phis = List.filter ~f:Fn.(not <<< is_true) phis in
        begin if List.exists ~f:is_false phis then
          Bool false
        else match phis with
          | []    -> Bool true
          | [phi] -> phi
          | _     -> And phis
        end
    | Formula.Or phis ->
        let phis = List.map ~f:formula phis in
        let phis = List.filter ~f:Fn.(not <<< is_false) phis in
        begin if List.exists ~f:is_true phis then
          Bool true
        else match phis with
          | []    -> Bool false
          | [phi] -> phi
          | _     -> Or phis
        end
    | phi -> phi
end

module Preprocess = struct
  (* gets hes_rule list. returns hes_rule list and toplevel name*)
  let translate_top top_rule = 
    let rec inner = function
      | Hflz.Abs(x, y) -> Hflz.Forall(x, inner y)
      | x -> x
    in
    let open Hflz in
    let body = inner top_rule.body in
    (* remove arguments of the template type *)
    let var = {top_rule.var with ty=TyBool(())} in
    {top_rule with body; var}

  let main psi = match psi with
    | [] -> [], None
    | top::xs -> translate_top top::xs, Some(top.var)
end