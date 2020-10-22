module Util        = Hflmc2_util
module Options     = Hflmc2_options
module Syntax      = Hflmc2_syntax
module Typing      = Hflmc2_typing
module Eldarica    = Eldarica

open Util
open Syntax

let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

type result = [ `Valid | `Invalid | `Unknown | `Fail]

let show_result = function
  | `Valid      -> "Valid"
  | `Invalid    -> "Invalid"
  | `Unknown    -> "Unknown"
  | `Fail       -> "Fail"

let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start

let times = Hashtbl.create (module String)
let add_mesure_time tag f =
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let all_start = Unix.gettimeofday ()
let report_times () =
  let total = Unix.gettimeofday() -. all_start in
  let kvs = Hashtbl.to_alist times @ [("total", total)] in
  match List.max_elt ~compare (List.map kvs ~f:(String.length<<<fst)) with
  | None -> Print.pr "no time records"
  | Some max_len ->
      Print.pr "Profiling:@.";
      List.iter kvs ~f:begin fun (k,v) ->
        let s =
          let pudding = String.(init (max_len - length k) ~f:(Fn.const ' ')) in
          "  " ^ k ^ ":" ^ pudding
        in Print.pr "%s %f sec@." s v
      end

let save_hes_to_file hes =
  Random.self_init ();
  let r = Random.int 0x10000000 in
  let file = Printf.sprintf "/tmp/%s-%d.smt2" "nuonly" r in
  let oc = open_out file in
  let fmt = Format.formatter_of_out_channel oc in
  Printf.fprintf oc "%%HES\n" ;
  Solver.A.hflz_hes' Print.simple_ty_ fmt hes;
  Format.pp_print_flush fmt ();
  file
  
let main file =
  let psi, _ = Syntax.parse_file file in
  Log.app begin fun m -> m ~header:"Input" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  let psi = Syntax.Trans.Simplify.hflz_hes psi in
  Log.app begin fun m -> m ~header:"Simplified" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  let psi = Solver.elim_mu_with_rec psi 0 0 in
  Log.app begin fun m -> m ~header:"Mu approx" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  Log.app begin fun m -> m ~header:"Mu approx2" "%a"
    (Solver.A.hflz_hes' Print.simple_ty_) psi
  end;
  print_int @@ List.length psi;
  print_string @@ "File name: " ^ save_hes_to_file psi ^ "\n";
  let psi, top = Syntax.Trans.Preprocess.main psi in
  match top with
  | Some(top) -> begin
    match Typing.main psi top with
    | `Sat ->  `Valid
    | `Unsat ->  `Invalid
    | `Unknown -> `Unknown
    | _ -> `Fail
    end
  | None -> print_string "[Warn]input was empty\n";
      `Valid (* because the input is empty *)

