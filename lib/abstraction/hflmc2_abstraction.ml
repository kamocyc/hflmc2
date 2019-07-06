open Hflmc2_util
open Hflmc2_syntax
open Type
module Option = Hflmc2_option

module Log = (val Logs.src_log @@ Logs.Src.create ~doc:"Predicate Abstraction" "Abstraction")

type env = abstraction_ty IdMap.t

(* options *)
let exhaustive_search = ref false


(* For Or and And: (λxs.u1, λxs.u2) -> λxs.f u1 u2 *)
let merge_lambda : int -> (Hfl.t list -> Hfl.t) -> Hfl.t list -> Hfl.t =
  fun len merge phis ->
    let new_vars = List.init len ~f:(fun _ -> Id.gen ATyBool) in
    let rec gather_vars len phi = match phi with
      | _ when len = 0 ->
          ([], phi)
      | Hfl.Abs(x, phi) ->
          let (xs, phi') = gather_vars (len-1) phi in
          (x::xs, phi')
      | _ ->
          let x = Id.gen ATyBool in
          let xs, phi = gather_vars (len-1) (Hfl.App(phi, Var(x))) in
          (x::xs, phi)
    in
    let rename orig_vars phi =
      let map =
        try IdMap.of_alist_exn @@ List.zip_exn
              (List.map ~f:Id.remove_ty orig_vars)
              (List.map ~f:Hfl.mk_var new_vars)
        with _ -> assert false
      in Subst.Hfl.hfl map phi
    in
    let phis' = List.map phis ~f:Fn.(uncurry rename <<< gather_vars len) in
    Hfl.mk_abss new_vars (merge phis')

(* Γ |- σ <= σ ↪ φ' で得たφ'にφを適用 *)
let rec abstract_coerce : env -> abstraction_ty -> abstraction_ty -> Hfl.t -> Hfl.t =
  fun env sigma sigma' phi ->
    let debug = false in
    if debug then begin
      Print.pr "==================@.";
      Print.print ~tag:"σ " Print.abstraction_ty sigma;
      Print.print ~tag:"σ'" Print.abstraction_ty sigma';
    end;
    match sigma, sigma' with
    | TyBool ps, TyBool qs ->
        (* x[j] is a variable for q[j] *)
        let xs = List.init (List.length qs) ~f:(fun _ -> Id.gen ATyBool) in
        begin
        try
          (* Simple case: forall p[i], there exists j_i s.t. p[i] = q[j_i] *)
          let qxs = List.zip_exn qs xs in
          (* gather x[j_i] *)
          let pxs = List.map ps ~f:begin fun p ->
              snd @@ List.find_exn qxs ~f:(fun (q,_) -> FpatInterface.(p <=> q))
            end
          in
          (* assemble *)
          let phi' = Hfl.mk_abss xs @@ Hfl.mk_apps phi (List.map ~f:Hfl.mk_var pxs) in
          phi'
        with Not_found ->
          if false then begin
            Print.print ~tag:"ps" Print.(list_comma formula) ps;
          end;
          (* Let ps be P1,...,Pk and qs be Q1,...,Ql.
           * To compute φ, find I ⊆ {1,...,l} and J1,...,Jm ⊆ {1,...,k} such that
           *    ∧ _{i \in I}Qi => ∨ _{h \in 1,...,m}∧ _{j \in Jh} Pj
           * Let
           *    φ'_{I,J1,...,Jm} = ∧ _{i \in I}b_i ∧ _{h \in 1,...,m} φ (1 \in Jh) ... (l \in Jh)
           * then φ' is the union of all φ'_{I,J1,...,Jm}.
           * *)
          let l = List.length qs in
          let k = List.length ps in
          let max_ors = !Option.Abstraction.max_ors in
          let one_to_l = List.(range ?start:(Some `inclusive) ?stop:(Some `exclusive) 0 l) in
          let one_to_k = List.(range ?start:(Some `inclusive) ?stop:(Some `exclusive) 0 k) in
          let _Is = List.powerset one_to_l in
          let _Js =
            List.filter (List.powerset one_to_k) ~f:begin fun _J ->
              let ps' = List.(map ~f:(nth_exn ps) _J) in
              FpatInterface.is_consistent_set ps' && not (List.is_empty _J)
            end
          in
          let _Jss =
            List.filter (List.powerset ~limit:max_ors _Js)
              ~f:(fun l -> not (List.is_empty l))
          in
          let phi's =
            List.map _Is ~f:begin fun _I ->
              let xs' = List.(map ~f:(nth_exn xs) _I) in
              let qs' = List.(map ~f:(nth_exn qs) _I) in
              let _Q  = Formula.mk_ands qs' in

              (* /\Q => \/i(/\Ji) を満たす極大の J1,...,Jh の集合を得る *)
              let ans =
                if FpatInterface.(_Q ==> Formula.Bool false)
                then
                  [[one_to_k]] (* /\{P1,...,Pk}が唯一の極大元 *)
                else if
                  (* See [FpatInterface.strongest_post_cond'] *)
                  FpatInterface.(Formula.Bool true ==> _Q) || !exhaustive_search
                then
                  let candidates : (int list list * Formula.t) list =
                    List.filter_map _Jss ~f:begin fun _Js ->
                      let pss =
                            List.map _Js ~f:begin fun _J ->
                              List.map _J ~f:begin fun j ->
                                List.nth_exn ps j end end
                      in
                      let body =
                            Formula.mk_ors @@ List.map ~f:Formula.mk_ands pss
                      in
                      if FpatInterface.(_Q ==> body)
                      then Some (_Js, body)
                      else None
                    end
                  in
                  if true (* もしかしたらバグってるかも知れない *)
                  then
                    let (<=) (_,p1) (_,p2) = FpatInterface.(p2 ==> p1) in
                    List.map ~f:fst @@ Fn.maximals' (<=) candidates
                  else
                    List.map ~f:fst candidates
                else
                  [FpatInterface.strongest_post_cond _Q ps]
              in
              let nodes = List.map ans ~f:begin fun _Js ->
                  let mk_atom _J =
                        Hfl.mk_apps phi @@
                          List.map one_to_k ~f:begin fun j ->
                            Hfl.Bool (List.mem ~equal:(=) _J j)
                          end
                  in
                  Hfl.mk_ands ~kind:`Inserted
                      @@ Hfl.mk_ands ~kind:`Inserted (List.map xs' ~f:Hfl.mk_var)
                      :: List.map _Js ~f:mk_atom
                end
              in
              (* log *)
              if true then List.iter ans ~f:begin fun _Js ->
                let pss =
                      List.map _Js ~f:begin fun _J ->
                        List.map _J ~f:begin fun j ->
                          List.nth_exn ps j end end
                in
                Log.debug begin fun m -> m ~header:"Coerce" "I = %a,@ J = %a"
                  Print.(list_set formula) qs'
                  Print.(list_set (list_set formula)) pss
                end;
              end;
              Hfl.mk_ors ~kind:`Inserted nodes
            end
          in
          let phi' = Hfl.mk_abss xs @@ Hfl.mk_ors ~kind:`Inserted phi's in
          phi'
        end
    | TyArrow({ty = TyInt; _} as x, sigma), TyArrow({ty = TyInt; _} as y, sigma') ->
        let sigma = Subst.Arith.abstraction_ty x (Arith.mk_var y) sigma in
        abstract_coerce env sigma sigma' phi
    | TyArrow({ty = TySigma sigma1 ; _}, sigma2 )
    , TyArrow({ty = TySigma sigma1'; _}, sigma2') ->
        let f = Id.gen ~name:"ac_f" (Type.abstract sigma) in
        let x = Id.gen ~name:"ac_x" (Type.abstract sigma1') in
        let phi1x = abstract_coerce env sigma1' sigma1 (Var x) in
        abstract_coerce env sigma2 sigma2' @@ App(Var f, phi1x)
    | _ -> assert false

let rec abstract_infer : env -> simple_ty Hflz.t -> Type.abstraction_ty * Hfl.t =
  fun env psi ->
    let (sigma, phi) : Type.abstraction_ty * Hfl.t = match psi with
      (* Var *)
      | Var v ->
          let sigma =
            try
              IdMap.lookup env v
            with _ ->
              Fn.fatal @@ Fmt.strf "Variable %s not found in environment" (Id.to_string v)
            in
          (sigma , Var { v with ty = Type.abstract sigma })
      (* Bool *)
      | Bool b ->
          let sigma = TyBool Formula.[Bool b] in
          (sigma, Hfl.mk_identity ATyBool)
      (* Pred-Simple *)
      | Pred(p,as') ->
          let sigma = TyBool Formula.[Pred(p,as')] in
          (sigma, Hfl.mk_identity ATyBool)

      (* Abs-Int *)
      | Abs({ty = TyInt; _} as v, psi) ->
          let (sigma, phi) = abstract_infer env psi in
          (TyArrow(v, sigma), phi)

      | App(psi, Arith a) ->
          begin match abstract_infer env psi with
          | TyArrow({ty = TyInt; _} as x, sigma), phi ->
              (Subst.Arith.abstraction_ty x a sigma, phi)
          | _ -> assert false
          end
      | App(psi1, psi2) ->
          begin match abstract_infer env psi1 with
          | TyArrow({ty = TySigma sigma'; _}, sigma), phi1 ->
              let phi2 = abstract_check env psi2 sigma' in
              (sigma, App(phi1, phi2))
          | _ -> assert false
          end

      (* And, Or *)
      | And psis | Or psis ->
          let make_ope = match psi with
            | And _ -> Hfl.mk_ands ~kind:`Original
            | Or _  -> Hfl.mk_ors  ~kind:`Original
            | _ -> assert false
          in
          let sigma_phis = List.map psis ~f:(abstract_infer env) in
          let preds' =
            List.remove_consecutive_duplicates ~equal:FpatInterface.(<=>) @@
              List.concat @@ List.map sigma_phis ~f:begin function
                | TyBool pred, _ -> pred
                | _ -> assert false
                end
          in
          let sigma' = TyBool preds' in
          let phis' = List.map sigma_phis ~f:begin fun (sigma, phi) ->
                abstract_coerce env sigma sigma' phi
            end
          in
          let phi' = merge_lambda (List.length preds') make_ope phis' in
          (sigma', phi')
      | Exists _ | Forall _ -> assert false (* unimplemented *)
      | Abs _ | Arith _ -> assert false (* impossible *)
          (* NOTE Absはpsiがβ-reduxを持たないという仮定の元でimpossible *)
    in
      let phi = Simplify.hfl ~force:false phi in
      Log.debug begin fun m -> m ~header:"Term" "@[<hv 0>%a@ ==> %a@;<1 1>⇢  %a@]"
        Print.(hflz simple_ty_) psi
        Print.abstraction_ty sigma
        Print.hfl phi
      end;
      sigma, phi

and abstract_check : env -> simple_ty Hflz.t -> Type.abstraction_ty -> Hfl.t =
  fun env psi sigma ->
    let phi : Hfl.t = match psi, sigma with
      | Abs({ty=TyInt;_} as x, psi), TyArrow({ty=TyInt;_} as x', sigma) ->
          let sigma = Subst.Id'.abstraction_ty x' {x with ty=`Int} sigma in
          abstract_check env psi sigma
      | Abs(x, psi), TyArrow({ty = TySigma sigma'; _}, sigma) ->
          let env' = IdMap.add env x sigma' in
          let x'   = Id.{ x with ty = Type.abstract sigma' } in
          Abs(x', abstract_check env' psi sigma)
      | _ ->
          let sigma', phi = abstract_infer env psi in
          abstract_coerce env sigma' sigma phi
    in
      let phi = Simplify.hfl ~force:false phi in
      Log.debug begin fun m -> m ~header:"Term" "@[<hv 0>%a@ <== %a@;<1 1>⇢  %a@]"
        Print.(hflz simple_ty_) psi
        Print.abstraction_ty sigma
        Print.hfl phi
      end;
      phi

let abstract_main : env -> simple_ty Hflz.t -> Hfl.t =
  fun env psi ->
    let sigma, phi = abstract_infer env psi in
    match sigma with
    | TyBool ps ->
        let complement = Formula.(mk_not (mk_ors ps)) in
        if FpatInterface.(complement ==> Formula.Bool false)
        then
          phi
          |> abstract_coerce env (TyBool ps) (TyBool [])
          |> Simplify.hfl
        else
          let ps' = complement::ps in
          phi
          |> abstract_coerce env (TyBool ps ) (TyBool ps')
          |> abstract_coerce env (TyBool ps') (TyBool [])
          |> Simplify.hfl
    | _ -> assert false

let abstract_rule : env -> simple_ty Hflz.hes_rule -> Hfl.hes_rule =
  fun env { var; body; fix } ->
    let aty = try IdMap.lookup env var with _ -> assert false in
    let rule' =
      Hfl.{ var  = Id.{ var with ty = Type.abstract aty }
          ; body = abstract_check env body aty
          ; fix  = fix
          }
    in
    begin Log.debug @@ fun m -> m ~header:"Nonterminal" "%a"
      Print.hfl_hes_rule rule'
    end;
    rule'

let abstract : env -> simple_ty Hflz.hes -> Hfl.hes =
  fun env hes -> match hes with
    | main::hes ->
        let main' =
          Hfl.{ var  = Id.{ main.var with ty = ATyBool }
              ; body = abstract_main env main.body
              ; fix  = main.fix
              }
        in
        begin Log.debug @@ fun m -> m ~header:"Nonterminal" "%a"
            Print.hfl_hes_rule main'
        end;
        main' :: List.map ~f:(abstract_rule env) hes
    | [] -> assert false

