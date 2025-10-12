type _ typ =
  | TBool : bool typ
  | TNat : int typ
  | TArrow : 'a typ * 'b typ -> ('a -> 'b) typ

type empty = Empty
type ('head, 'tail) env = Env

type (_, _) index =
  | IZ : ('a, ('a, _) env) index
  | IS : ('a, ('b, 'env) env) index -> ('a, ('c, ('b, 'env) env) env) index

type (_, _) term =
  | Var : ('a, 'env) index -> ('a, 'env) term
  | Abs : 'a typ * ('b, ('a, 'env) env) term -> ('a -> 'b, 'env) term
  | App : ('a -> 'b, 'env) term * ('a, 'env) term -> ('b, 'env) term
  | True : (bool, 'env) term
  | False : (bool, 'env) term
  | If :
      (bool, 'env) term * ('a, 'env) term * ('a, 'env) term
      -> ('a, 'env) term
  | Zero : (int, 'env) term
  | Succ : (int, 'env) term -> (int, 'env) term

let id_bool : (bool -> bool, empty) term = Abs (TBool, Var IZ)
let const_true : (bool -> bool, empty) term = Abs (TBool, True)
let apply_id_true : (bool, empty) term = App (id_bool, True)

let first_arg : (bool -> int -> bool, empty) term =
  Abs (TBool, Abs (TNat, Var (IS IZ)))

let _ = App (App (first_arg, True), Zero)
