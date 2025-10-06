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

let rec of_list = function
  | [] -> Ex (VNil, Z)
  | x :: xs ->
      let (Ex (v, k)) = of_list xs in
      Ex (VCons (x, v), S k)

let rec filter : type a n. (a -> bool) -> (a, n) vec -> a ex_vec =
 fun p v ->
  match v with
  | VNil -> Ex (VNil, Z)
  | VCons (x, xs) ->
      let (Ex (ys, k)) = filter p xs in
      if p x then Ex (VCons (x, ys), S k) else Ex (ys, k)

let rec nat_to_int : type n. n nat -> int = function
  | Z -> 0
  | S n -> 1 + nat_to_int n

let length (Ex (_, k)) = nat_to_int k
let head : type a n. (a, n succ) vec -> a = function VCons (x, _) -> x

(* Type-level addition:
   The proof that m + n = p at the type level. *)
type (_, _, _) plus =
  | PlusZ : (zero, 'n, 'n) plus (* zero + n = n *)
  | PlusS :
      ('m, 'n, 'p) plus (* if m + n = p, *)
      -> ('m succ, 'n, 'p succ) plus (* then (m+1) + n = (p+1) *)

(* Lemma: takes a proof of m + n = p and returns a proof of m + (n + 1) = p + 1. *)
let rec plus_succ : type m n p. (m, n, p) plus -> (m, n succ, p succ) plus =
  function
  | PlusZ -> PlusZ
  | PlusS p -> PlusS (plus_succ p)

(* Lemma: n + zero = n. *)
let rec plus_n_zero : type n. n nat -> (n, zero, n) plus = function
  | Z -> PlusZ
  | S n -> PlusS (plus_n_zero n)

(* Appending a vector of length m to a vector of length n yields a vector of length p,
   if we can supply a proof of m + n = p. *)
let rec append : type a m n p.
    (m, n, p) plus -> (a, m) vec -> (a, n) vec -> (a, p) vec =
 fun plus xs ys ->
  match (plus, xs) with
  | PlusZ, VNil -> ys
  | PlusS p, VCons (x, xs') -> VCons (x, append p xs' ys)

let rec map : type a b n. (a -> b) -> (a, n) vec -> (b, n) vec =
 fun f v -> match v with VNil -> VNil | VCons (x, xs) -> VCons (f x, map f xs)

let tail (Ex (v, n)) =
  let t : type a n. (a, n succ) vec -> (a, n) vec = function
    | VCons (_, xs) -> xs
  in
  match n with Z -> failwith "" | S n -> Ex (t v, n)

type (_, _) eq = Refl : ('a, 'a) eq

let rec eq_nat : type n m. n nat -> m nat -> (n, m) eq option =
 fun n m ->
  match (n, m) with
  | Z, Z -> Some Refl
  | S n', S m' -> (
      match eq_nat n' m' with Some Refl -> Some Refl | None -> None)
  | _, _ -> None

let zip (Ex (v1, n1)) (Ex (v2, n2)) =
  let rec z : type a b n. (a, n) vec -> (b, n) vec -> (a * b, n) vec =
   fun v1 v2 ->
    match (v1, v2) with
    | VNil, VNil -> VNil
    | VCons (x, xs), VCons (y, ys) -> VCons ((x, y), z xs ys)
  in
  match eq_nat n1 n2 with Some Refl -> Ex (z v1 v2, n1) | None -> failwith ""

(* Reverse: *)
let rec reverse_aux : type a m n p.
    (m, n, p) plus -> (a, m) vec -> (a, n) vec -> (a, p) vec =
 fun plus xs acc ->
  match (plus, xs) with
  | PlusZ, VNil -> acc
  | PlusS p, VCons (x, xs') -> reverse_aux (plus_succ p) xs' (VCons (x, acc))

let reverse v =
  (* let rec length : type n. ('a, n) vec -> n nat = function *)
  (*   | VNil -> Z *)
  (*   | VCons (_, xs) -> S (length xs) *)
  (* in *)
  match v with
  | Ex (v, k) -> Ex (reverse_aux (plus_n_zero k) v VNil, k)

let rec print_vec : type n. ('a, n) vec -> ('a -> unit) -> unit =
 fun v print ->
  match v with
  | VNil -> print_endline "[]"
  | VCons (x, xs) ->
      print x;
      print_string " ";
      print_vec xs print

let rec get : type a n k. (a, n succ) vec -> (n succ, k) fin -> a option =
 fun v idx ->
  match (v, idx) with
  | VCons (x, _), FZ -> Some x
  | VCons (_, xs), FS k' -> (
      match xs with VNil -> None | VCons _ -> get xs k')
