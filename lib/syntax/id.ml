open Hflmc2_util

(** ['ty] is typically a type of the id *)
type 'ty t =
  { name : string
  ; id   : int
  ; ty   : 'ty
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let eq x y = String.equal x.name y.name && x.id = y.id

let counter = new Fn.counter
let gen_id () = counter#tick

let to_string id =
  let c = String.get id.name 0 in
  if c = Char.uppercase c
  then id.name
  else id.name ^ string_of_int id.id

let gen : ?name:string -> 'annot -> 'anno t =
  fun ?(name="x") ann ->
    let id = gen_id() in
    print_string @@ "gen name: " ^ name ^ ", id: " ^ string_of_int id ^ "\n";
    { name = name
    ; id = id
    ; ty = ann
    }

let remove_ty : 'ty t -> unit t = fun x -> { x with ty = () }

module Key = struct
  type nonrec t = unit t
  let sexp_of_t = sexp_of_t sexp_of_unit
  let t_of_sexp = t_of_sexp unit_of_sexp
  let compare : t -> t -> int = compare Core.Unit.compare
  let hash : t -> int = String.hash <<< to_string
end

