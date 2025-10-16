module type SYM = sig
  type 'a repr

  val int : int -> 'a repr
  val bool : bool -> 'a repr
  val add : 'a repr -> 'a repr -> 'a repr
  val lam : ('a repr -> 'b repr) -> ('a -> 'b) repr
  val app : ('a -> 'b) repr -> 'a repr -> 'b repr
  val if_ : bool repr -> 'a repr -> 'a repr -> 'a repr
end

module Eval : SYM = struct
  type 'a repr = 'a

  let int x = x
  let bool x = x
  let add = ( + )
  let lam f = f
  let app f x = f x
  let if_ c t e = if c then t else e
end

module Pretty : SYM = struct
  type 'a repr = string

  let int = string_of_int
  let bool = string_of_bool
  let add x y = "(" ^ x ^ " + " ^ y ^ ")"

  let lam f =
    let x = "x" in
    "(fun " ^ x ^ " -> " ^ f x ^ ")"

  let app f x = f ^ " " ^ x
  let if_ c t e = "if " ^ c ^ " then " ^ t ^ " else " ^ e
end

let () =
  let value =
    let open Eval in
    app (lam (fun x -> add x (int 1))) (if_ (bool true) (int 41) (int 0))
  in
  let bool_value =
    let open Pretty in
    if_ (bool true) (int 1) (int 0)
  in
  Printf.printf "Eval: %d\n" value;
  Printf.printf "Pretty bool: %s\n" bool_value
