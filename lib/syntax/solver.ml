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

let to_args : 'ty Type.ty -> 'ty Type.ty Type.arg Id.t list = fun ty -> 
  let rec rep =
    fun acc ty -> match ty with
    | Type.TyArrow (arg, ty) -> (
      rep (arg::acc) ty
    )
    | Type.TyBool b -> acc in
  rep [] ty
    
let to_abs : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) = fun args ->
  let name_map = List.map (fun arg -> (arg.Id.name, Id.gen ~name:arg.Id.name arg.Id.ty)) args in
  fun body -> 
    let rec rep = function
      | [] -> body
      | arg::xs -> Abs (List.assoc arg.Id.name name_map, rep xs) in
    rep args

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


  (* | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty t * 'ty t
  | And    of 'ty t * 'ty t
  | Abs    of 'ty arg Id.t * 'ty t
  | Forall of 'ty arg Id.t * 'ty t
  | App    of 'ty t * 'ty t
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list *)

(* type ctype
  = TycInt
  | TyBool *)

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

(* Type.simple_ty hes_rule list *)
  
let type_check_arith : ty_env -> Arith.t -> bool = fun env arith ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_arg = Type.show_arg show_arg_ty in
  let show_id = Id.show Fmt.nop in
  let rec rep = fun arith -> match arith with
  | Arith.Int _ -> true
  | Arith.Var ({Id.ty;_} as v) -> begin
    match List.find_opt (fun k -> Id.eq k v) env with
    | Some {Id.ty=ty'; _} ->
      if ty' = Type.TyInt
      then true
      else failwith @@ "[Arith] var `" ^ show_id v ^ "`'s type should be Int, but actual: " ^ show_arg ty' ^ "."
    | None -> failwith @@ "[Arith] unbound var `" ^ show_id v ^ "`' "
  end
  | Arith.Op (op, args) ->
    List.length args = 2 &&
    List.for_all rep args in
  rep arith

let get_hflz_type : ty_env -> Type.simple_ty Hflz.t -> Type.simple_ty = fun env hfl ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_arg = Type.show_arg show_arg_ty in
  let show_ty = Type.show_ty Fmt.nop in
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
        | _ -> assert false
    end
    | TyArrow ({ty=TySigma ty; _}, tybody) -> begin
      let ty2 = rep env f2 in
      if ty2 = ty
      then tybody
      else assert false
    end
    | TyBool _ -> failwith @@ "App: f1 should not be boolean."
  end
  | Pred (p, args) -> begin
    List.iter (fun arg -> if type_check_arith env arg then () else assert false) args;
    let arg_num = List.length args in
    if arg_num <> 2 then assert false;
    Type.TyBool ()
  end
  | Arith _ -> assert false in
  rep env hfl
  (* Type.simple_ty Type.arg Id.t *)
let type_check : Type.simple_ty hes -> unit = fun hes ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_ty = Type.show_ty Fmt.nop in
  let show_arg = Type.show_arg show_arg_ty in
  let show_id = Id.show Fmt.nop in
  let env = List.map (fun {var={ty;_} as var;_} -> {var with ty=Type.TySigma ty}) hes in
  List.iter (fun ({var={ty;name;id}; body; _}) -> 
    (* print_string @@ "name=" ^ name ^ "\n"; *)
    let ty' = get_hflz_type env body in
    if not @@ eq_modulo_arg_ids ty' ty then failwith @@ "rule type mismatch (Checked type: " ^ show_ty ty' ^ " / Env type: " ^ show_ty ty ^ ")"
  ) hes

(* 変換した述語の呼び出し元を置換 *)
let replace_caller : Type.simple_ty hes -> Type.simple_ty Hflz.t -> Type.simple_ty Id.t list -> (Type.simple_ty Hflz.t * Type.simple_ty hes) =
  fun hes hfl preds ->
    let new_rules = ref [] in
    let rec rep : Type.simple_ty Hflz.t -> Type.simple_ty Hflz.t = fun hfl -> match hfl with
      | Var id' -> begin
        (* TODO: IDのeqが正しく判定される？ *)
        match List.find_opt (fun pred -> Id.eq pred id') preds with
        | Some id -> begin
          (* 処理対象のpredicateであるとき *)
          let new_rec_var = Id.gen ~name:"forall_y" Type.TyInt in
          let new_rec_var_f = {new_rec_var with ty = `Int} in
          let abs = to_abs @@ to_args id'.ty in
          let vars = to_vars (abs @@ Bool true) in
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
    | Abs (arg, child) -> rep1 child
    | _ -> hfl in
    rep1 hfl)
    
(* Type.simple_ty Hflz.hes = unit ty hes_rule list *)
let elim_mu_with_rec (hes : Type.simple_ty Hflz.hes) (coe1 : int) (coe2 : int) : Type.simple_ty Hflz.hes =
  (* calc outer_mu_funcs *)
  (* これが何をやっているのか不明。hesはトップレベルの述語の情報は別途持っていて、それ以外は参照グラフから再構成する必要があるということ？listだから、順番の情報はあると思うが *)
  (* let outer_mu_funcs = get_outer_mu_funcs funcs in *)
  (* make tvars *)
  (*  *)
  type_check hes;
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
        |> List.map (fun ({var; body;_} as level) ->
          let rec_var = make_rec_var var.Id.name in
          (level, rec_var, {var with Id.ty=Type.TyArrow({rec_var with ty=TyInt}, var.Id.ty)})) in
      let nu_vars = nu_level
        |> List.map (fun ({var; body;_} as level) ->
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
      (* Log.app begin fun m -> m ~header:"new_level" "%a"
        Print.(hflz_hes simple_ty_) new_level
      end; *)
      let new_rules = ref [] in
      let rem_level = rem_level |> List.map (fun ({var; body; fix} as rule) -> 
        let body, new_rules' = replace_caller hes body (List.map (fun (_, _, v) -> v) @@ nu_vars @ mu_vars) in
        new_rules := new_rules' @ !new_rules;
        {rule with body = body}
      ) in
      new_level @ !new_rules @ (rep rem_level) in
  let hes = rep hes in
  Log.app begin fun m -> m ~header:"Mu approx" "%a"
    Print.(hflz_hes simple_ty_) hes
  end;
  type_check hes;
  hes
  