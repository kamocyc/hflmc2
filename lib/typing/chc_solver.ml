open Hflmc2_syntax
open Hflmc2_options
open Chc
open Rtype


(* set of template *)

let selected_cmd size = 
  let rec inner sv = 
    if sv = "z3" then 
      [|"z3"; "fp.engine=spacer"|]
    else if sv = "hoice" then 
      [|"hoice"|]
    else if sv = "fptprove" then
      [|"fptprove"; "--synthesizer"; "dt"; "--format"; "clp"; "--problem"; "psat"; "-edq"; "-edrc"; "-epp"; "-fq"; "20"; "--format"; "smt-lib2"|]
    else
      failwith "selected solver is not found"
  in
  let sv = !Typing.solver in
  if sv = "auto" then
    begin
      if size > 1 then
        inner "fptprove"
      else
        inner "hoice"
    end
  else inner sv

let prologue = "(set-logic HORN)
"

let epilogue = "\
(check-sat)
(get-model)
"

let rec collect_preds chcs m = 
  let rec inner rt m = match rt with 
  | RTemplate (p, l) -> Rid.M.add p (List.length l) m
  | RAnd(x, y) | ROr(x, y) ->
    m |> inner x |> inner y
  | _ -> m
  in
  match chcs with
  | [] -> m
  | chc::chcs ->
    m |> inner chc.body |> inner chc.head |> collect_preds chcs

let collect_vars chc = 
  let collect_from_arith a m =
    let fvs = Arith.fvs a in
    List.fold_left IdSet.add m fvs
  in
  let rec collect_from_ariths ars m = match ars with
    | [] -> m
    | x::xs -> 
      m |> collect_from_arith x |> collect_from_ariths xs
  in
  let rec inner rt m = match rt with
  | RTemplate(_, l) | RPred(_, l) -> 
    collect_from_ariths l m
  | RAnd(x, y) | ROr(x, y) -> 
    m |> inner x |> inner y
  | _ -> m
  in 
  IdSet.empty |> inner chc.head |> inner chc.body

let rec gen_len_args len = 
  if len < 1 then ""
  else if len = 1 then "Int"
  else "Int " ^ gen_len_args (len - 1)

let pred_def (name, len) =
  gen_len_args len |> Printf.sprintf "(declare-fun %s (%s) Bool)\n" (Rid.to_string name)

let var_def id = id |> Id.to_string |> Printf.sprintf "(%s Int)"

let op2smt2 = 
  let open Arith in
  function
  | Add -> "+"
  | Sub -> "-"
  | Mult -> "*"

let pred2smt2 pred args = 
  let open Formula in
  Printf.sprintf 
  begin
    match pred with
    | Eq -> "(= %s)"
    | Neq -> "(not (= %s))"
    | Le -> "(<= %s)"
    | Ge -> "(>= %s)"
    | Lt -> "(< %s)"
    | Gt -> "(> %s)"
  end args

let rec arith2smt2 = 
  let open Arith in
  function 
  | Int x -> Printf.sprintf "%d" x
  | Var id -> Id.to_string id
  | Op (op, l) -> 
    let args = ariths2smt2 l in
    let op_s = op2smt2 op in
    Printf.sprintf "(%s %s)" op_s args
and ariths2smt2 l =
    l |> List.map arith2smt2 |> List.fold_left (fun s x -> s ^ " " ^ x) "" 

let template2smt2 (p, l) =
  let name = Rid.to_string p in
  let args = ariths2smt2 l in
    Printf.sprintf "(%s %s)" name args

let pred2smt2 (p, l) =
  let args = ariths2smt2 l in
  pred2smt2 p args

let rec ref2smt2 rt = match rt with
  | RTrue -> "true"
  | RFalse -> "false"
  | RAnd(x, y) -> Printf.sprintf "(and %s %s)" (ref2smt2 x) (ref2smt2 y)
  | ROr(x, y) -> Printf.sprintf "(or%s %s)" (ref2smt2 x) (ref2smt2 y)
  | RTemplate(p, l) -> template2smt2 (p, l)
  | RPred(p, l) -> pred2smt2(p, l)

let gen_assert chc =
  let vars = collect_vars chc in
  let vars_s = vars |> IdSet.to_list |> List.map var_def |> List.fold_left (^) "" in
  let body = ref2smt2 chc.body in
  let head = ref2smt2 chc.head in
  let s = Printf.sprintf "(=> %s %s)" body head in
  Printf.sprintf "(assert (forall (%s) %s))\n" vars_s s

let chc2smt2 chcs = 
  let preds = collect_preds chcs Rid.M.empty in
  let def = preds |> Rid.M.bindings |> List.map pred_def |> List.fold_left (^) "" in
  let body = chcs |> List.map gen_assert |> List.fold_left (^) "" in
  prologue ^ def ^ body ^ epilogue


let parse_model model = 
  let open Hflmc2_util in
  (* Ported from Iwayama san's parser 
     https://github.com/Hogeyama/hflmc2/blob/0c29b0b3a8aacb2496615244b3d93e98370c6eee/lib/refine/hornClauseSolver.ml#L215-L280
  *)
  let open Sexp in
  let fail f s = invalid_arg @@ f ^ ": " ^ Sexp.to_string s in
  let mk_var name =
     Id.{ name; id=0; ty=`Int }
  in
  let parse_arg = function
    | List [Atom v; Atom "Int" ] -> mk_var v
    | s -> fail "parse_arg" s
  in
  let rec parse_arith = function
    | Atom s ->
        begin match int_of_string s with
        | n -> Arith.mk_int n
        | exception _ -> Arith.mk_var' (mk_var s)
        end
    | List (Atom op :: ss) ->
        let op = match op with
          | "+" -> Arith.Add
          | "-" -> Arith.Sub
          | "*" -> Arith.Mult
          | s   -> fail "parse_arith:op" (Atom s)
        in
          begin
          match ss with
          | [] -> failwith "program error(parse_arith)"
          | [x] -> begin
              let e = 
              match op with 
              | Arith.Add | Arith.Sub -> 0
              | Arith.Mult -> 1
              in
              Arith.mk_op op [Arith.Int(e); parse_arith x]
            end
          | _ -> 
            let [@warning "-8"] a::as' = List.map ss ~f:parse_arith in
              List.fold_left ~init:a as' ~f:begin fun a b ->
                Arith.mk_op op [a; b]
              end
            end
    | s -> fail "parse_arith" s
  in
  let rec parse_formula = function
    | Atom "true"  -> RTrue
    | Atom "false" -> RFalse
    | List (Atom a :: ss) ->
        let a = match a with
          | "="   -> `Pred Formula.Eq
          | "!="  -> `Pred Formula.Neq
          | "<="  -> `Pred Formula.Le
          | ">="  -> `Pred Formula.Ge
          | "<"   -> `Pred Formula.Lt
          | ">"   -> `Pred Formula.Gt
          | "and" -> `And 
          | "or"  -> `Or 
          | "not" -> `Not 
          | s     -> fail "parse_formula:list" (Atom s)
        in
        begin match a with
        | `Pred pred ->
            RPred (pred, (List.map ~f:parse_arith ss))
        | `And ->
            let  [@warning "-8"] a::as' = List.map ss ~f:parse_formula in
            List.fold_left ~init:a as' ~f:(fun x y -> RAnd(x, y))
        | `Or -> 
            let  [@warning "-8"] a::as' = List.map ss ~f:parse_formula in
            List.fold_left ~init:a as' ~f:(fun x y -> ROr(x, y))
        | `Not -> 
            let [@warning "-8"] [f] = List.map ss ~f:parse_formula in
            negate_ref f
        end
    | s -> fail "parse_formula" s
  in
  let parse_def = function
    | List [Atom "define-fun"; Atom id; List args; Atom "Bool"; body] ->
        let args = List.map ~f:parse_arg args in
        let body = parse_formula body in
        let id = Scanf.sscanf id "X%d" (fun x -> x) in
        (id, args, body)
    | s -> fail "parse_def" s
  in
  print_string model;
  match Sexplib.Sexp.parse model with
  | Done(model, _) -> begin 
    match model with
    | List (Atom "model" :: sol) ->
        Ok(List.map ~f:parse_def sol)
    | _ -> Error "parse_model" 
    end
  | _ -> Error "failed to parse model"

let check_sat chcs size = 
  let open Hflmc2_util in
  let smt2 = chc2smt2 chcs in
  Random.self_init ();
  let r = Random.int 0x10000000 in
  let file = Printf.sprintf "tmp/%d.smt2" r in
  let oc = open_out file in
  Printf.fprintf oc "%s" smt2;
  close_out oc;
  let cmd = selected_cmd size in
  let _, out, _ = Fn.run_command ~timeout:20.0 (Array.concat [cmd; [|file|]]) in
  match String.lsplit2 out ~on:'\n' with
  | Some ("unsat", _) -> `Unsat
  | Some ("sat", model) ->
    let open Hflmc2_options in
    if !Typing.show_refinement then
      `Sat(parse_model model)
    else
      `Sat(Error "did not calculate refinement. Use --show-refinement")
  | Some ("unknown", _) -> `Unknown
  | _ -> (Printf.printf "Failed to handle the result of chc solver\n\n%s\n" out; `Fail)