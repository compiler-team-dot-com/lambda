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

let rec foldi (f : int -> int -> int) (z : int) : int list -> int = function
  | [] -> z
  | h :: t -> f h (foldi f z t)

let rec fold (f : 'a -> 'a -> 'a) (z : 'a) : 'a list -> 'a = function
  | [] -> z
  | h :: t -> f h (foldi f z t)

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

(* Second approach *)
type ('a, 'b) app = ..
type list_name
type ('a, 'b) app += List_name : 'a list -> ('a, list_name) app

let inj x = List_name x
let[@warning "-8"] prj (List_name x) = x

type ('a, 'n) seq = { decon : ('a, 'n) app -> ('a * ('a, 'n) app) option }

let rec folds (m : 'a monoid) (s : ('a, 'n) seq) : ('a, 'n) app -> 'a =
 fun c ->
  match s.decon c with None -> m.unit | Some (h, t) -> m.op h (folds m s t)

let sums s c = folds monoid_plus s c

let list_seq : ('a, list_name) seq =
  {
    decon =
      (fun (List_name l) ->
        match l with [] -> None | h :: t -> Some (h, List_name t));
  }
