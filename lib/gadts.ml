type 'a tree =
  | Empty : 'a tree
  | Tree : 'a tree * 'a * 'a tree -> 'a tree

let rec depth : 'a. 'a tree -> int = function
  | Empty -> 0
  | Tree (left, _, right) -> 1 + max (depth left) (depth right)

let top : 'a. 'a tree -> 'a option = function
  | Empty -> None
  | Tree (_, v, _) -> Some v

let rec swivel : 'a. 'a tree -> 'a tree = function
  | Empty -> Empty
  | Tree (left, v, right) -> Tree (swivel right, v, swivel left)

type 'a ntree =
  | EmptyN : 'a ntree
  | TreeN : 'a * ('a * 'a) ntree -> 'a ntree

let rec depthN : 'a. 'a ntree -> int = function
  | EmptyN -> 0
  | TreeN (_, t) -> 1 + depthN t

let topN : 'a. 'a ntree -> 'a option = function
  | EmptyN -> None
  | TreeN (v, _) -> Some v

let id x = x

let swivelN p =
  let rec swiv : 'a. ('a -> 'a) -> 'a ntree -> 'a ntree =
   fun f t ->
    match t with
    | EmptyN -> EmptyN
    | TreeN (v, t) -> TreeN (f v, swiv (fun (x, y) -> (f y, f x)) t)
  in
  swiv id p

type z = Z : z
type 'n s = S : 'n -> 'n s

let three = S (S (S Z))

type ('a, _) gtree =
  | EmptyG : ('a, z) gtree
  | TreeG : ('a, 'n) gtree * 'a * ('a, 'n) gtree -> ('a, 'n s) gtree

let rec depthG : type a n. (a, n) gtree -> n = function
  | EmptyG -> Z
  | TreeG (left, _, _) -> S (depthG left)

let topG : type a n. (a, n s) gtree -> a = function TreeG (_, v, _) -> v

let rec swivelG : type a n. (a, n) gtree -> (a, n) gtree = function
  | EmptyG -> EmptyG
  | TreeG (left, v, right) -> TreeG (swivelG right, v, swivelG left)

(* A max function for type-level natural numbers *)
type (_, _, _) max =
  | MaxEq : 'a -> ('a, 'a, 'a) max
  | MaxFlip : ('a, 'b, 'c) max -> ('b, 'a, 'c) max
  | MaxSuc : ('a, 'b, 'a) max -> ('a s, 'b, 'a s) max

(* given a max proof, return the maximum *)
let rec max : type a b c. (a, b, c) max -> c = function
  | MaxEq x -> x
  | MaxSuc m -> S (max m)
  | MaxFlip m -> max m

type ('a, _) dtree =
  | EmptyD : ('a, z) dtree
  | TreeD :
      ('a, 'm) dtree * 'a * ('a, 'n) dtree * ('m, 'n, 'o) max
      -> ('a, 'o s) dtree

let depthD : type a n. (a, n) dtree -> n = function
  | EmptyD -> Z
  | TreeD (_, _, _, o) -> S (max o)

let topD : type a n. (a, n s) dtree -> a = function TreeD (_, v, _, _) -> v

let rec swivelD : type a n. (a, n) dtree -> (a, n) dtree = function
  | EmptyD -> EmptyD
  | TreeD (left, v, right, o) ->
      TreeD (swivelD right, v, swivelD left, MaxFlip o)

(* Some properties of type equality *)
type (_, _) eql = Refl : ('a, 'a) eql

let symm : type a b. (a, b) eql -> (b, a) eql = fun Refl -> Refl

let trans : type a b c. (a, b) eql -> (b, c) eql -> (a, c) eql =
 fun Refl Refl -> Refl

module Lift (T : sig
  type _ t
end) : sig
  val lift : ('a, 'b) eql -> ('a T.t, 'b T.t) eql
end = struct
  let lift : type a b. (a, b) eql -> (a T.t, b T.t) eql = fun Refl -> Refl
end

let cast : type a b. (a, b) eql -> a -> b = fun Refl x -> x

(* Encoding other GADTs with eql *)
type ('a, 'n) etree =
  | EmptyE : ('n, z) eql -> ('a, 'n) etree
  | TreeE :
      ('n, 'm s) eql * ('a, 'm) etree * 'a * ('a, 'm) etree
      -> ('a, 'n) etree

let rec depthE : type a n. (a, n) etree -> n = function
  | EmptyE Refl -> Z
  | TreeE (Refl, left, _, _) -> S (depthE left)
