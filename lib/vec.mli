type zero = Zero
type 'n succ = Succ

type _ nat =
  | Z : zero nat
  | S : 'n nat -> 'n succ nat

type (_, _) vec =
  | VNil : ('a, zero) vec
  | VCons : 'a * ('a, 'n) vec -> ('a, 'n succ) vec

type 'a ex_vec = Ex : ('a, 'n) vec * 'n nat -> 'a ex_vec

type (_, _) fin =
  | FZ : ('n succ, zero) fin (* 0 < n+1 *)
  | FS : ('n, 'k) fin -> ('n succ, 'k succ) fin (* k+1 < n+1 *)

type (_, _) eq = Refl : ('a, 'a) eq

(* Type-level addition:
   The proof that m + n = p at the type level. *)
type (_, _, _) plus =
  | PlusZ : (zero, 'n, 'n) plus (* zero + n = n *)
  | PlusS :
      ('m, 'n, 'p) plus (* if m + n = p, *)
      -> ('m succ, 'n, 'p succ) plus (* then (m+1) + n = (p+1) *)

val eq_nat : 'n nat -> 'm nat -> ('n, 'm) eq option
val nat_to_int : 'n nat -> int
val of_list : 'a list -> 'a ex_vec
val filter : ('a -> bool) -> ('a, 'n succ) vec -> 'a ex_vec
val length : 'a ex_vec -> int
val head : ('a, 'n succ) vec -> 'a
val print_vec : ('a, 'n) vec -> ('a -> unit) -> unit
val reverse : 'a ex_vec -> 'a ex_vec
val zip : 'a ex_vec -> 'b ex_vec -> ('a * 'b) ex_vec
val tail : 'a ex_vec -> 'a ex_vec
val get : 'a 'n 'k. ('a, 'n succ) vec -> ('n succ, 'k) fin -> 'a option
val append : ('m, 'n, 'p) plus -> ('a, 'm) vec -> ('a, 'n) vec -> ('a, 'p) vec
val map : ('a -> 'b) -> ('a, 'n) vec -> ('b, 'n) vec
