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
