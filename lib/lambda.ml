(* Types. *)
type _ ty =
  | TInt : int ty
  | TBool : bool ty
  | TFun : 'a ty * 'b ty -> ('a -> 'b) ty

(* Expressions. *)
type _ expr =
  | LitInt : int -> int expr
  | LitBool : bool -> bool expr
  | Add : int expr * int expr -> int expr
  | Eq : int expr * int expr -> bool expr
  | Var : string -> 'a expr
  | Lam : string * 'a ty * 'b expr -> ('a -> 'b) expr
  | App : ('a -> 'b) expr * 'a expr -> 'b expr

(* Generate fresh variable names. *)
let fresh () =
  let counter = ref 0 in
  fun prefix ->
    incr counter;
    prefix ^ "_" ^ string_of_int !counter

(* Alpha-renaming substitution. *)
let rec substitute : type a. string -> a expr -> a expr -> a expr =
 fun x v e -> failwith "not implemented"
