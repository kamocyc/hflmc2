module Syntax = Hflmc2_syntax

open Syntax
open Hflz

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

let get_next_level : 'ty Hflz.hes -> ('ty Hflz.hes * 'ty Hflz.hes) =
  fun hes -> match hes with
    | [] -> ([], [])
    (* TODO: ネストのレベルの向き合っている？ *)
    | ({fix; _})::_ -> begin
      let rec rep acc = function
        | [] -> (acc, [])
        | ({fix=fix'; _} as eq)::eqs -> 
          if fix = fix'
          then rep (eq::acc) eqs
          else (acc, eq::eqs)
      in
      rep [] hes
    end

let get_next_mu_level : 'ty Hflz.hes -> ('ty Hflz.hes * 'ty Hflz.hes * 'ty Hflz.hes) =
  fun hes -> 
    (* TODO: リストの反転を無くす *)
    let (next_level, remain_level) = get_next_level @@ List.rev hes in
    match next_level with 
    | [] -> ([], [], [])
    | ({fix; _}::_) -> begin
      let (next_level', remain_level') = get_next_level remain_level in
      match fix with
      | Fixpoint.Greatest -> 
        (next_level, next_level', remain_level')
      | Fixpoint.Least -> 
        ([], next_level, remain_level)
    end

let replace_var_occurences : ('ty Id.t -> 'ty Hflz.t) -> 'ty Hflz.t -> 'ty Hflz.t =
  fun subst hfl -> 
  (* TODO: IDのeqが正しく判定される？ *)
  let rec rep = function
    | Var   id -> subst (id)
    | Bool   b -> Bool b
    | Or (f1, f2) -> Or (rep f1, rep f2)
    | And (f1, f2) -> And (rep f1, rep f2)
    | Abs (v, f1) -> Abs (v, rep f1)
    | Forall (v, f1) -> Forall (v, rep f1)
    | App (f1, f2) -> App (rep f1, rep f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t)
  in
  (* predicateはboolean以外を返すことは無い。arithmeticの中にhfl predicateは現れない *)
  rep hfl
  
let replace_mu_var_occurences : [`Int] Id.t -> Type.simple_ty Hflz.t -> Type.simple_ty Id.t -> 'ty Hflz.t =
  fun var_y hfl sub_var -> 
    replace_var_occurences
      (fun id -> if Id.eq id sub_var then App (Var sub_var, Arith (Op (Sub, [Var var_y; Int 1]))) else Var id)
      hfl

let replace_nu_var_occurences : [`Int] Id.t -> Type.simple_ty Hflz.t -> Type.simple_ty Id.t -> 'ty Hflz.t =
  fun var_y hfl sub_var -> 
    replace_var_occurences
      (fun id -> if Id.eq id sub_var then App (Var id, Arith (Var var_y)) else Var id)
      hfl

(* Arrow type to list of types of the arguments conversion *)
let to_args : 'ty Type.ty -> 'ty Type.ty Type.arg Id.t list =
  let rec rep =
    fun acc ty -> match ty with
    | Type.TyArrow (arg, ty) -> rep (arg::acc) ty
    | Type.TyBool _ -> acc in
  rep []

(* 引数のリストからabstractionに変換 *)
let to_abs : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) = fun args ->
  let name_map = List.map (fun arg -> (arg.Id.name, Id.gen ~name:arg.Id.name arg.Id.ty)) args in
  fun body -> 
    let rec rep = function
      | [] -> body
      | arg::xs -> Abs (List.assoc arg.Id.name name_map, rep xs) in
    rep args

(* Absの引数のIDを新規に生成しない版 *)
let to_abs' : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) =
  fun args body ->
    let rec go = function
      | [] -> body
      | arg::xs -> Abs(arg, go xs) in
    go args
    
(* Abstractionから、それに適用する変数の列を生成 *)
let to_vars : 'ty Hflz.t -> ('ty Hflz.t -> 'ty Hflz.t) = fun hfl ->
  fun body ->
    let rec rep: 'ty Hflz.t -> 'ty Hflz.t = function
      | Abs ({id;ty;name}, child) -> begin
        match ty with
        | Type.TyInt -> 
          (* TODO: これはたぶん引数の順番が逆になる *)
          App (rep child, Arith (Var {name; id; ty=`Int}))
        | Type.TySigma x -> 
          App (rep child, Var {name; id; ty=x})
      end
      | _ -> body in
    rep hfl

let get_rule : 'ty Id.t -> 'ty hes -> 'ty hes_rule =
  fun id hes ->
    match List.find_opt (fun {var;_} -> Id.eq var id) hes with
    | None -> assert false
    | Some rule -> rule

type ty_env = (Type.simple_ty Type.arg Id.t) list

let eq_modulo_arg_ids : Type.simple_ty -> Type.simple_ty -> bool =
  let rec rep = fun ty1 ty2 -> match ty1, ty2 with
  | Type.TyBool _, Type.TyBool _ -> true
  | Type.TyArrow ({ty=ty1;_}, body1), Type.TyArrow({ty=ty2;_}, body2) -> begin
    let tyf =
      match ty1, ty2 with
      | Type.TySigma ty1', Type.TySigma ty2' ->
        rep ty1' ty2'
      | Type.TyInt, Type.TyInt -> true
      | _ -> false in
    tyf && rep body1 body2
  end
  | _ -> false in
  rep
  
let type_check_arith : ty_env -> Arith.t -> bool = fun env arith ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_arg = Type.show_arg show_arg_ty in
  let show_id = Id.show Fmt.nop in
  let rec rep = fun arith -> match arith with
  | Arith.Int _ -> true
  | Arith.Var v -> begin
    match List.find_opt (fun k -> Id.eq k v) env with
    | Some {Id.ty=ty'; _} ->
      if ty' = Type.TyInt
      then true
      else failwith @@ "[Arith] var `" ^ show_id v ^ "`'s type should be Int, but actual: " ^ show_arg ty' ^ "."
    | None -> failwith @@ "[Arith] unbound var `" ^ show_id v ^ "`' "
  end
  | Arith.Op (_, args) ->
    List.length args = 2 &&
    List.for_all rep args in
  rep arith

let get_hflz_type : ty_env -> Type.simple_ty Hflz.t -> Type.simple_ty = fun env hfl ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_arg = Type.show_arg show_arg_ty in
  let show_id = Id.show Fmt.nop in
  let rec rep : ty_env -> Type.simple_ty Hflz.t -> Type.simple_ty = fun env 
  hfl -> match hfl with
  | Bool _ -> Type.TyBool ()
  | Var ({ty;_} as v) -> begin
    (* 環境に出現していることをチェック *)
    (* ここで出ているVarは、Int型ではない。Int型変数はArith内に出る *)
    match List.find_opt (fun k -> Id.eq k v) env with
    | Some {ty=ty';_} -> 
      if Type.TySigma ty = ty'
      then ty
      else failwith @@ "Var: `" ^ (show_id v) ^ "` type mismatch (expected: " ^ (show_arg @@ Type.TySigma ty) ^ " / actual: " ^ (show_arg ty')  ^ ")"
    | None -> failwith @@ "Var: unbound variable (" ^ (show_id v) ^ ")"
  end
  | Or (f1, f2) -> begin
    if rep env f1 = Type.TyBool () && rep env f2 = Type.TyBool ()
    then Type.TyBool ()
    else assert false
  end
  | And (f1, f2) -> begin
    if rep env f1 = Type.TyBool () && rep env f2 = Type.TyBool ()
    then Type.TyBool ()
    else assert false
  end
  | Abs (arg, body) -> begin
    Type.TyArrow (arg, rep (arg::env) body)
  end
  | Forall (arg, body) -> begin
    rep (arg::env) body
  end
  | App (f1, f2) -> begin
    let ty1 = rep env f1 in
    match ty1 with
    (* 唯一subformulaにIntが許される *)
    | TyArrow ({ty=TyInt; _}, tybody) -> begin
      match f2 with
        | Arith arith -> 
          if type_check_arith env arith
          then tybody
          else assert false
        | _ -> failwith @@ "App: f2 should be arithmetic expression"
    end
    | TyArrow ({ty=TySigma ty; _}, tybody) -> begin
      let ty2 = rep env f2 in
      if ty2 = ty
      then tybody
      else assert false
    end
    | TyBool _ -> failwith @@ "App: f1 should not be boolean."
  end
  | Pred (_, args) -> begin
    List.iter (fun arg -> if type_check_arith env arg then () else assert false) args;
    let arg_num = List.length args in
    if arg_num <> 2 then assert false;
    Type.TyBool ()
  end
  | Arith _ -> assert false in
  rep env hfl
  
let type_check : Type.simple_ty hes -> unit = fun hes ->
  let show_ty = Type.show_ty Fmt.nop in
  let env = List.map (fun {var={ty;_} as var;_} -> {var with ty=Type.TySigma ty}) hes in
  List.iter (fun ({var={ty;_}; body; _}) -> 
    let ty' = get_hflz_type env body in
    if not @@ eq_modulo_arg_ids ty' ty then failwith @@ "rule type mismatch (Checked type: " ^ show_ty ty' ^ " / Env type: " ^ show_ty ty ^ ")"
  ) hes

(* 変換した述語の呼び出し元を置換 *)
let replace_caller : Type.simple_ty Hflz.t -> Type.simple_ty Id.t list -> (Type.simple_ty Hflz.t * Type.simple_ty hes) =
  fun hfl preds ->
    let new_rules = ref [] in
    let rec rep : Type.simple_ty Hflz.t -> Type.simple_ty Hflz.t = fun hfl -> match hfl with
      | Var id' -> begin
        (* TODO: IDのeqが正しく判定される？ *)
        match List.find_opt (fun pred -> Id.eq pred id') preds with
        | Some id -> begin
          (* 処理対象のpredicateであるとき *)
          let new_rec_var = Id.gen ~name:"forall_y" Type.TyInt in
          let new_rec_var_f = {new_rec_var with ty = `Int} in
          (* predicateの型から引数を取得 *)
          (* TODO: predicateが部分適用されているときにうまくいく？ *)
          let abs = to_abs @@ to_args id'.ty in
          let vars = to_vars (abs @@ (* Dummy *) Bool true) in
          (* TODO: Int 10じゃなくてうまく決める *)
          Forall (new_rec_var, abs @@ Or (Pred (Formula.Lt, [Var new_rec_var_f; Int 10]), vars @@ App (Var id, Arith (Var new_rec_var_f))))
(*        let ref_rule = get_rule id hes in
          (* TODO: forallを別途処理する *)
          let new_rec_var = Id.gen ~name:"forall_y" Type.TyInt in
          let new_rec_var_f = {new_rec_var with ty = `Int} in
          let new_rule_id = Id.gen ~name:("forall_" ^ id.name) (Type.TyArrow (new_rec_var, id.ty)) in
          let new_rule = {
            var = new_rule_id;
            (* TODO: ヒューリスティックで決める *)
            body = (
              let args = to_args id.ty in
              let abs = to_abs args in
              let vars = to_vars args in
              abs @@ And (Or (Pred (Formula.Lt, [Var new_rec_var_f; Int 10]), vars @@ App (Var id, Arith (Var new_rec_var_f))), vars @@ App (Var new_rule_id, Arith (Op (Add, [Var new_rec_var_f; Int 1]))))
            );
            fix = Fixpoint.Greatest } in
          new_rules := new_rule :: !new_rules;
          App (Var new_rule_id, Arith (Int 0)) *)
        end
        | None -> Var id'
      end
      | Bool   b -> Bool b
      | Or (f1, f2) -> Or (rep f1, rep f2)
      | And (f1, f2) -> And (rep f1, rep f2)
      | Abs (v, f1) -> Abs (v, rep f1)
      | Forall (v, f1) -> Forall (v, rep f1)
      | App (f1, f2) -> App (rep f1, rep f2)
      | Arith t -> Arith t
      | Pred (p, t) -> Pred (p, t)
    in
    (* predicateはboolean以外を返すことは無い。arithmeticの中にhfl predicateは現れない *)
    (rep hfl, !new_rules)

let extract_head_abstracts : Type.simple_ty Hflz.t -> ((Type.simple_ty Hflz.t -> Type.simple_ty Hflz.t) * Type.simple_ty Hflz.t) = fun hfl -> 
  ((fun body ->     
    let rec rep2 = fun hfl -> match hfl with
    | Abs (arg, child) -> Abs(arg, rep2 child)
    | _ -> body in
    rep2 hfl),
  let rec rep1 = fun hfl -> match hfl with
    | Abs (_, child) -> rep1 child
    | _ -> hfl in
    rep1 hfl)

let to_arrow_type : Type.simple_ty Type.arg Id.t list -> Type.simple_ty = fun args ->
  let rec go acc args = match args with
    | arg::xs -> begin
      go (Type.TyArrow (arg, acc)) xs
    end
    | [] -> acc in
  go (Type.TyBool ()) (List.rev args)
(* 
let get_occurrences phi =
  let vars = ref [] in
  let rec go phi = match phi with
    | Var _ | Bool _ | Arith _ |  Pred _ -> phi
    | Or (phi1,phi2) -> Or(go phi1, go phi2)
    | And(phi1,phi2) -> And(go phi1, go phi2)
    | App(phi1,phi2) -> App(go phi1, go phi2)
    | Abs(x, _)    -> begin
    end
    | Forall (x,phi) -> begin
      foralls := (x, 0) :: !foralls;
      Forall (x, go phi)
    end
     *)

let args_ids_to_apps (ids : 'ty Type.arg Id.t list) : ('ty Hflz.t -> 'ty Hflz.t) = fun body ->
  let rec go ids = match ids with
    | x::xs -> begin
      match x.Id.ty with
      | Type.TySigma t -> begin
        App (go xs, Var {x with ty=t})
      end
      | Type.TyInt -> begin
        App (go xs, Arith (Var {x with ty=`Int}))
      end
    end
    | [] -> body in
  go @@ List.rev ids

let rec fvs_with_type : 'ty Hflz.t -> 'ty Type.arg Id.t list = function
  | Var x          -> [{ x with ty = Type.TySigma x.ty}]
  | Bool _         -> []
  | Or (phi1,phi2) -> (fvs_with_type phi1) @ (fvs_with_type phi2)
  | And(phi1,phi2) -> (fvs_with_type phi1) @ (fvs_with_type phi2)
  | App(phi1,phi2) -> (fvs_with_type phi1) @ (fvs_with_type phi2)
  | Abs(x, phi)    -> List.filter (fun t -> not @@ Id.eq t x) @@ fvs_with_type phi(* listだと、ここが毎回線形時間になる... *)
  | Forall(x, phi) -> List.filter (fun t -> not @@ Id.eq t x) @@ fvs_with_type phi
  | Arith a        -> List.map (fun id -> {id with Id.ty = Type.TyInt}) @@ Arith.fvs a
  | Pred (_, as')   -> as' |> List.map (fun a -> Arith.fvs a |> List.map (fun id -> {id with Id.ty = Type.TyInt})) |> List.flatten


(* phiの中のlambdaをdecomposeする *)
let decompose_lambda_ (phi : Type.simple_ty Hflz.t) (rule_id : Type.simple_ty Id.t) (hes : Type.simple_ty hes) =
  let hes_var_names = List.map (fun {var; _} -> Id.remove_ty var) hes in
  let extract_abstraction phi not_apply_vars =
    let xs, phi' = decompose_abs phi in
    (* 型情報も入っている。 *)
    (* arithの中のfvも見ている *)
    let free_vars = fvs_with_type phi in
    let free_vars = List.filter (fun v -> not @@ List.exists (fun v' -> Id.eq v' (Id.remove_ty v)) @@ not_apply_vars @ hes_var_names) free_vars in
    List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string "") free_vars;
    let arr_type = to_arrow_type xs in
    (* 一般にはAbsが連続するので、連続したAbsをまとめて切り出したい *)
    (* 内部の式が外部の変数を参照することはあるのか => TODO: integer変数では有りうる。しかしまだ実装していない *)
    let new_rule_id = Id.gen ~name:(rule_id.name ^ "_sub" ^ string_of_int (Random.int 100)) arr_type in
    let new_rule = {
      var = new_rule_id;
      body = phi';
      fix = Fixpoint.Greatest } in
    let new_sub_formula = args_ids_to_apps free_vars @@ Var new_rule_id in
    (new_sub_formula, new_rule, free_vars @ xs) in
  let new_rules = ref [] in
  let rec go phi = match phi with
    | Var _ | Bool _ | Arith _ |  Pred _ -> phi
    | Or (phi1,phi2) -> Or(go phi1, go phi2)
    | And(phi1,phi2) -> And(go phi1, go phi2)
    | App(phi1,phi2) -> App(go phi1, go phi2)
    | Abs(_, _)    -> begin
      let v, new_rule, xs = extract_abstraction phi [Id.remove_ty rule_id] in
      new_rules := ({new_rule with body = to_abs' xs new_rule.body}) :: !new_rules;
      v
    end
    | Forall (x, phi) -> begin
      (* TODO: 直下にlambdaがあるとき以外にも対応させる。 *)
      match phi with
      | Abs _ -> begin
        let v, {var; body; fix}, free_vars = extract_abstraction phi (Id.remove_ty x :: [Id.remove_ty rule_id]) in
        new_rules := {var; body=(to_abs' free_vars (Forall (x, body))); fix} :: !new_rules;
        v
      end
      | _ -> Forall(x, go phi)
    end
  in
  (* 先頭のAbstractionとforallは読み飛ばす *)
  let rec go' phi = match phi with
    | Abs(x, phi) -> begin
      Abs(x, go' phi)
    end
    | _ -> go phi
  in
  Log.app begin fun m -> m ~header:"original formula" "%a"
    Print.(hflz simple_ty_) phi
  end;
  let res = go' phi in
  Log.app begin fun m -> m ~header:"convered formula" "%a"
    Print.(hflz simple_ty_) res
  end;
  Log.app begin fun m -> m ~header:"added_rules" "%a"
    Print.(hflz_hes simple_ty_) !new_rules
  end;
  (!new_rules, res)

let decompose_lambdas hes (rule : Type.simple_ty hes_rule) = 
  let rec go ({body; var; _} as rule) = 
    let new_rules, res = decompose_lambda_ body var hes in
    match new_rules with
    | [] -> [{rule with body = res}]
    | xs -> begin
      let xs = List.map (fun r -> go r) xs in
      {rule with body = res} :: List.flatten xs
    end in
  go rule

let move_first f ls =
  let l1, l2 = List.partition f ls in
  l1 @ l2

(* Type.simple_ty Hflz.hes = unit ty hes_rule list *)
let elim_mu_with_rec (hes : Type.simple_ty Hflz.hes) (coe1 : int) (coe2 : int) : Type.simple_ty Hflz.hes =
  (* calc outer_mu_funcs *)
  (* これが何をやっているのか不明。hesはトップレベルの述語の情報は別途持っていて、それ以外は参照グラフから再構成する必要があるということ？listだから、順番の情報はあると思うが *)
  (* let outer_mu_funcs = get_outer_mu_funcs funcs in *)
  (* make tvars *)
  (*  *)
  type_check hes;
  if List.length hes = 0 then failwith "EMPTY HES";
  let {var=original_top_level_predicate;_} = List.nth hes 0 in
  let rec rep : Type.simple_ty Hflz.hes -> Type.simple_ty Hflz.hes = fun hes -> 
    (* 最下層のmuを取得 *)
    (* どっちが下（内側）のレベルなのか？ *)
    let nu_level, mu_level, rem_level = get_next_mu_level hes in
    Log.app begin fun m -> m ~header:"nu_level" "%a"
      Print.(hflz_hes simple_ty_) nu_level
    end;
    Log.app begin fun m -> m ~header:"mu_level" "%a"
      Print.(hflz_hes simple_ty_) mu_level
    end;
    Log.app begin fun m -> m ~header:"rem_level" "%a"
      Print.(hflz_hes simple_ty_) rem_level
    end;
    let make_rec_var name = Id.gen ~name:("rec_" ^ name) `Int in
    match mu_level with
    | [] -> hes
    | mu_level -> 
      let mu_vars = mu_level
        |> List.map (fun ({var; _} as level) ->
          let rec_var = make_rec_var var.Id.name in
          (level, rec_var, {var with Id.ty=Type.TyArrow({rec_var with ty=TyInt}, var.Id.ty)})) in
      let nu_vars = nu_level
        |> List.map (fun ({var; _} as level) ->
          let rec_var = make_rec_var var.Id.name in
          (level, rec_var, {var with Id.ty=Type.TyArrow({rec_var with ty=TyInt}, var.Id.ty)})) in
      print_string @@ "len=" ^ string_of_int @@ List.length nu_vars;
      (* 置換 *)
      let new_level = (nu_vars @ mu_vars) |> List.map (fun ({body; fix; _}, rec_var, var) ->
        let head_abstacts, body = extract_head_abstracts body in
        (* 型: `IntはFormulaの中で使われる（Predの型で規定）、TypIntは述語の型で使う *)
        (* TODO: 名前の生成方法はこれでいいか確認 *)
        let body = mu_vars
          |> List.fold_left (fun body (_, _, mu_var) -> replace_mu_var_occurences rec_var body mu_var) body in
        let body = nu_vars
          |> List.fold_left (fun body (_, _, nu_var) -> replace_nu_var_occurences rec_var body nu_var) body in
        let body =
          head_abstacts @@ match fix with
          | Fixpoint.Least -> 
            And (Pred (Formula.Ge, [Var rec_var; Int 0]), body)
          | Fixpoint.Greatest ->
            body in
        let body = Abs ({rec_var with ty=TyInt}, body) in
        {var; body; fix=Fixpoint.Greatest}
      ) in
      let new_rules = ref [] in
      let rem_level = rem_level |> List.map (fun ({body; _} as rule) -> 
        (* TODO: replace_callerにhesを渡さなくて本当に良いのか？ *)
        let body, new_rules' = replace_caller body (List.map (fun (_, _, v) -> v) @@ nu_vars @ mu_vars) in
        new_rules := new_rules' @ !new_rules;
        {rule with body = body}
      ) in
      new_level @ !new_rules @ (rep rem_level) in
  let hes = rep hes in
  let hes = List.map (decompose_lambdas hes) hes |> List.flatten
    |> move_first (fun {var; _} -> var.name = original_top_level_predicate.name) in
  type_check hes;
  hes

module A = struct
  open Print
    
  let rec hflz_' : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty Hflz.t Fmt.t =
    fun format_ty_ prec ppf (phi : 'ty Hflz.t) -> match phi with
      | Bool true -> Fmt.string ppf "true1"
      | Bool false -> Fmt.string ppf "false"
      | Var x -> id ppf x
      | Or(phi1,phi2)  ->
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ || %a@]"
            (hflz_' format_ty_ Prec.or_) phi1
            (hflz_' format_ty_ Prec.or_) phi2
      | And (phi1,phi2)  ->
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ && %a@]"
            (hflz_' format_ty_ Prec.and_) phi1
            (hflz_' format_ty_ Prec.and_) phi2
      | Abs (x, psi) ->
        (* TODO: failwith *)
          show_paren (prec > Prec.abs) ppf "@[<1>λ%a:%a.@,%a@]"
            id x
            (argty (format_ty_ Prec.(succ arrow))) x.ty
            (hflz_' format_ty_ Prec.abs) psi
      | Forall (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (* (argty (format_ty_ Prec.(succ arrow))) x.ty *)
            (hflz_' format_ty_ Prec.abs) psi
      | App (psi1, psi2) ->
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
            (hflz_' format_ty_ Prec.app) psi1
            (hflz_' format_ty_ Prec.(succ app)) psi2
      | Arith a ->
          arith_ prec ppf a
      | Pred (pred, as') ->
          show_paren (prec > Prec.eq) ppf "%a"
            formula (Formula.Pred(pred, as'))
  
  (* let rec hflz_entry_' : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty Hflz.t Fmt.t =
    fun format_ty_ prec ppf (phi : 'ty Hflz.t) -> match phi with
      | Forall (x, psi) ->
        (* 別にあったら落とせばいい。 *)
        hflz_entry_' format_ty_ prec ppf psi 
      | Abs (x, psi) ->
        fail
      | psi -> hflz_' format_ty_ prec ppf psi *)
  
  let fprint_space f () = fprintf f " "
  
  let hflz' : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.t Fmt.t =
    fun format_ty_ -> hflz_' format_ty_ Prec.zero
    
  let hflz_hes_rule' : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes_rule Fmt.t =
    fun format_ty_ ppf rule ->
      let args, phi = decompose_abs rule.body in
      (* 'ty Type.arg Id.t を表示したい *)
      Fmt.pf ppf "@[<2>%s %a =%a@ %a.@]"
        (Id.to_string rule.var)
        (pp_print_list ~pp_sep:fprint_space id) args
        (* (format_ty_ Prec.zero) rule.var.ty *)
        fixpoint rule.fix
        (hflz' format_ty_) phi

  let hflz_hes' : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes Fmt.t =
    fun format_ty_ ppf hes ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule' format_ty_)) hes

end
