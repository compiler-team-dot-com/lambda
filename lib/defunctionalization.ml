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
