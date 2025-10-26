let rec fold : type a b. (a * b -> b) * b * a list -> b =
 fun (f, u, l) -> match l with [] -> u | x :: xs -> f (x, fold (f, u, xs))

let sum l = fold ((fun (x, y) -> x + y), 0, l)
let add (n, l) = fold ((fun (x, l') -> (x + n) :: l'), [], l)
let[@warning "-8"] 3 = sum [ 1; 1; 1 ]
let[@warning "-8"] [ 2; 2; 2 ] = add (1, [ 1; 1; 1 ])

type (_, _) arrow =
  | Fn_plus : (int * int, int) arrow
  | Fn_plus_cons : int -> (int * int list, int list) arrow

let apply : type a b. (a, b) arrow * a -> b =
 fun (appl, v) ->
  match appl with
  | Fn_plus ->
      let x, y = v in
      x + y
  | Fn_plus_cons n ->
      let x, l' = v in
      (x + n) :: l'

let rec fold : type a b. (a * b, b) arrow * b * a list -> b =
 fun (f, u, l) ->
  match l with [] -> u | x :: xs -> apply (f, (x, fold (f, u, xs)))

let sum l = fold (Fn_plus, 0, l)
let add (n, l) = fold (Fn_plus_cons n, [], l)
let[@warning "-8"] 3 = sum [ 1; 1; 1 ]
let[@warning "-8"] [ 2; 2; 2 ] = add (1, [ 1; 1; 1 ])

(* Higher kind poly *)
(* https://okmij.org/ftp/ML/higher-kind-poly.html *)

let rec sumi : int list -> int = function [] -> 0 | h :: t -> h + sumi t
let[@warning "-8"] 3 = sumi [ 1; 2 ]

let rec foldi (f : int -> int -> int) (z : int) : int list -> int = function
  | [] -> z
  | h :: t -> f h (foldi f z t)

let[@warning "-8"] 3 = foldi ( + ) 0 [ 1; 2 ]

let rec fold (f : 'a -> 'a -> 'a) (z : 'a) : 'a list -> 'a = function
  | [] -> z
  | h :: t -> f h (fold f z t)

let[@warning "-8"] 3 = fold ( + ) 0 [ 1; 2 ]

type 'a monoid = {
  op : 'a -> 'a -> 'a;
  unit : 'a;
}

(* bounded polymorphism *)
let rec foldm (m : 'a monoid) : 'a list -> 'a = function
  | [] -> m.unit
  | h :: t -> m.op h (foldm m t)

(* Examples *)
let monoid_plus : int monoid = { op = ( + ); unit = 0 }
let[@warning "-8"] 6 = foldm monoid_plus [ 1; 2; 3 ]
let monoid_maxchar : char monoid = { op = max; unit = Char.chr 0 }
let[@warning "-8"] 'c' = foldm monoid_maxchar [ 'b'; 'c'; 'a' ]

(* This won't work:

type ('a,'F) seq = {decon: 'a 'F -> ('a * 'a 'F) option}

let rec folds (m: 'a monoid) (s: ('a,'F) seq) : 'a 'F -> 'a = fun c ->
  match s.decon c with None -> m.unit | Some (h,t) -> m.op h (folds m s t)

*)

(* Using the module language: *)
module type seq_i = sig
  type 'a t

  val decon : 'a t -> ('a * 'a t) option
end

module FoldS (S : seq_i) = struct
  let rec fold (m : 'a monoid) : 'a S.t -> 'a =
   fun c ->
    match S.decon c with None -> m.unit | Some (h, t) -> m.op h (fold m t)
end

module SumS (S : seq_i) = struct
  open S
  open FoldS (S)

  let sum : int t -> int = fold monoid_plus
end

module ListS = struct
  type 'a t = 'a list

  let decon = function [] -> None | h :: t -> Some (h, t)
end

let[@warning "-8"] 3 =
  let module M = SumS (ListS) in
  M.sum [ 1; 2 ]

module ArrS = struct
  type 'a t = int * 'a array

  let decon (i, a) =
    if i >= Array.length a || i < 0 then None else Some (a.(i), (i + 1, a))
end

let[@warning "-8"] 3 =
  let module M = SumS (ArrS) in
  M.sum (0, [| 1; 2 |])

(* Second approach *)
type ('a, 'b) app = ..
type list_name
type ('a, 'b) app += List_name : 'a list -> ('a, list_name) app

let inj x = List_name x
let[@warning "-8"] prj (List_name x) = x
let[@warning "-8"] [ 1; 2 ] = prj @@ inj [ 1; 2 ]

type ('a, 'n) seq = { decon : ('a, 'n) app -> ('a * ('a, 'n) app) option }

let rec folds (m : 'a monoid) (s : ('a, 'n) seq) : ('a, 'n) app -> 'a =
 fun c ->
  match s.decon c with None -> m.unit | Some (h, t) -> m.op h (folds m s t)

let sums s c = folds monoid_plus s c

let[@warning "-8"] list_seq : ('a, list_name) seq =
  {
    decon =
      (fun (List_name l) ->
        match l with [] -> None | h :: t -> Some (h, List_name t));
  }

let[@warning "-8"] 3 = sums list_seq (List_name [ 1; 2 ])

(* Algebras *)

(* DSL of addition *)
module type add_i = sig
  type repr

  val int : int -> repr
  val add : repr -> repr -> repr
end

(* Term as a functor *)
module AddEx1 (I : add_i) = struct
  open I

  let res = add (add (int 1) (int 2)) (int 3)
end

(* A function that uses the add interfacce: parameterized by the
implementation of the interface: add a term to itself n times. *)
module NTimes (I : add_i) = struct
  include I

  let rec ntimes : int -> repr -> repr =
   fun n x ->
    if n <= 0 then int 0 else if n = 1 then x else add x (ntimes (n - 1) x)
end

(* Usage example, using the earlier AddEx1 *)
module AddEx2 (I : add_i) = struct
  open NTimes (I)
  module M = AddEx1 (I)

  let res = ntimes 3 M.res
end

let _ =
  (* An interpreter *)
  let module R : add_i with type repr = int = struct
    type repr = int

    let int = Fun.id
    let add = ( + )
  end in
  let[@warning "-8"] 18 =
    let module M = AddEx2 (R) in
    M.res
  in
  ()

(* All functors. We would like terms.
Using first-class modules, turn add_i (a sig) to an ordinary type. *)
type 'r add_t = (module add_i with type repr = 'r)

let add_ex1 : type r. r add_t -> r =
 fun (module I) -> I.(add (add (int 1) (int 2)) (int 3))

let rec ntimes : type r. r add_t -> int -> r -> r =
 fun (module I) n x ->
  let open I in
  if n <= 0 then int 0
  else if n = 1 then x
  else add x (ntimes (module I) (n - 1) x)

let add_ex2 : type r. r add_t -> r = fun repr -> ntimes repr 3 (add_ex1 repr)

let _ =
  (* An interpreter *)
  let module R : add_i with type repr = int = struct
    type repr = int

    let int = Fun.id
    let add = ( + )
  end in
  let[@warning "-8"] 18 =
    let r : int add_t = (module R) in
    add_ex2 r
  in
  ()

module type sym = sig
  type 'a repr

  val int : int -> int repr
  val add : int repr -> int repr -> int repr
  val iszero : int repr -> bool repr
  val if_ : bool repr -> 'a repr -> 'a repr -> 'a repr
end

(* a sample term of the DSL -- as a functor *)
module SymEx1 (I : sym) = struct
  open I

  let t1 = add (add (int 1) (int 2)) (int 3) (* intermediate binding *)
  let res = if_ (iszero t1) (int 0) (add t1 (int 1))
end

(* First interpreter: evaluator *)
module R : sym with type 'a repr = 'a = struct
  type 'a repr = 'a

  let int = Fun.id
  let add = ( + )
  let iszero = ( = ) 0
  let if_ b th el = if b then th else el
end

(* Second interpreter: a printer *)
module S : sym with type 'a repr = string = struct
  type 'a repr = string

  let paren x = "(" ^ x ^ ")"

  let int x =
    let t = string_of_int x in
    if x >= 0 then t else paren t

  let add e1 e2 = paren @@ e1 ^ " + " ^ e2
  let iszero x = paren @@ "iszero " ^ x
  let if_ b th el = "if " ^ b ^ " then " ^ th ^ " else " ^ el
end

(* Can now run the examples *)
let[@warning "-8"] 7 =
  let module M = SymEx1 (R) in
  M.res

let[@warning "-8"] "if (iszero ((1 + 2) + 3)) then 0 else (((1 + 2) + 3) + 1)" =
  let module M = SymEx1 (S) in
  M.res

module type symF = sig
  type a

  module Term (I : sym) : sig
    val res : a I.repr
  end
end

type 'a sym_term = (module symF with type a = 'a)

let sym_ex1 : _ sym_term =
  (module struct
    type a = int

    module Term = SymEx1
  end)

(* evaluation: a bit cumbersome *)
let _ =
  let module N = (val sym_ex1) in
  let module M = N.Term (R) in
  M.res

module SymSelf : sym with type 'a repr = 'a sym_term = struct
  type 'a repr = 'a sym_term

  let int : int -> int repr =
   fun n ->
    let module M (I : sym) = struct
      let res = I.int n
    end in
    (module struct
      type a = int

      module Term = M
    end)

  let add : int repr -> int repr -> int repr =
   fun (module E1) (module E2) ->
    let module M (I : sym) = struct
      module E1T = E1.Term (I)
      module E2T = E2.Term (I)

      let res = I.add E1T.res E2T.res
    end in
    (module struct
      type a = int

      module Term = M
    end)

  let iszero : int repr -> bool repr =
   fun (module E) ->
    let module M (I : sym) = struct
      module ET = E.Term (I)

      let res = I.iszero ET.res
    end in
    (module struct
      type a = bool

      module Term = M
    end)

  let if_ : type ar. bool repr -> ar repr -> ar repr -> ar repr =
   fun (module E) (module E1) (module E2) ->
    let module M (I : sym) = struct
      module ET = E.Term (I)
      module E1T = E1.Term (I)
      module E2T = E2.Term (I)

      let res = I.if_ ET.res E1T.res E2T.res
    end in
    (module struct
      type a = ar

      module Term = M
    end)
end

let sym_ex1 =
  let open SymSelf in
  let t1 = add (add (int 1) (int 2)) (int 3) in
  if_ (iszero t1) (int 0) (add t1 (int 1))

let _ = sym_ex1
