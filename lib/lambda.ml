type _ ty =
  | TInt : int ty
  | TBool : bool ty
  | TFun : 'a ty * 'b ty -> ('a -> 'b) ty

type _ expr =
  | LitInt : int -> int expr
  | LitBool : bool -> bool expr
  | Add : int expr * int expr -> int expr
  | Eq : int expr * int expr -> bool expr
  | Var : string * 'a ty -> 'a expr
  | Lam : string * 'a ty * 'b expr -> ('a -> 'b) expr
  | App : ('a -> 'b) expr * 'a expr -> 'b expr

(* existential wrapper for substitution values *)
type packed_val = PackVal : 'a ty * 'a expr -> packed_val

(* equality witness GADT *)
type (_, _) eq = Refl : ('x, 'x) eq

(* structural equality on types producing a witness when equal *)
let rec ty_eq : type a b. a ty -> b ty -> (a, b) eq option =
 fun ta tb ->
  match (ta, tb) with
  | TInt, TInt -> Some Refl
  | TBool, TBool -> Some Refl
  | TFun (a1, b1), TFun (a2, b2) -> (
      match (ty_eq a1 a2, ty_eq b1 b2) with
      | Some Refl, Some Refl -> Some Refl
      | _ -> None)
  | _ -> None

(* fresh name generator *)
let fresh =
  let counter = ref 0 in
  fun prefix ->
    incr counter;
    prefix ^ "_" ^ string_of_int !counter

(* compute free variables (simple, ok for examples) *)
let rec free_vars_expr : type a. a expr -> string list = function
  | LitInt _ | LitBool _ -> []
  | Add (e1, e2) | Eq (e1, e2) -> free_vars_expr e1 @ free_vars_expr e2
  | Var (x, _) -> [ x ]
  | Lam (x, _, body) -> List.filter (fun y -> y <> x) (free_vars_expr body)
  | App (f, arg) -> free_vars_expr f @ free_vars_expr arg

(* capture-avoiding substitution using a packed value and ty_eq *)
let rec substitute : type a. string -> packed_val -> a expr -> a expr =
 fun x pv e ->
  match e with
  | LitInt _ | LitBool _ -> e
  | Add (e1, e2) -> Add (substitute x pv e1, substitute x pv e2)
  | Eq (e1, e2) -> Eq (substitute x pv e1, substitute x pv e2)
  | Var (y, ty_y) ->
      if x = y then
        match pv with
        | PackVal (ty_v, v) -> (
            (* try to prove ty_v = ty_y; if so, we can safely return v *)
            match ty_eq ty_v ty_y with
            | Some Refl -> v (* typechecker learns v : a expr here *)
            | None -> failwith "Type mismatch in substitution")
      else Var (y, ty_y)
  | Lam (y, ty_y, body) ->
      if x = y then
        (* binder shadows x: do not substitute under it *)
        Lam (y, ty_y, body)
      else
        let pv_free = match pv with PackVal (_, v) -> free_vars_expr v in
        if List.mem y pv_free then
          (* alpha-rename y to avoid capture *)
          let y' = fresh y in
          let renamed_body =
            substitute y (PackVal (ty_y, Var (y', ty_y))) body
          in
          Lam (y', ty_y, substitute x pv renamed_body)
        else Lam (y, ty_y, substitute x pv body)
  | App (f, arg) -> App (substitute x pv f, substitute x pv arg)

(* small-step semantics: is_value and step *)
exception Stuck

let is_value : type a. a expr -> bool = function
  | LitInt _ | LitBool _ | Lam _ -> true
  | _ -> false

let rec step : type a. a expr -> a expr = function
  | App (Lam (x, ty_x, body), v) when is_value v ->
      (* when applying a lambda, pack the argument with its declared type *)
      substitute x (PackVal (ty_x, v)) body
  | App (f, arg) when not (is_value f) -> App (step f, arg)
  | App (f, arg) -> App (f, step arg)
  | Add (LitInt n1, LitInt n2) -> LitInt (n1 + n2)
  | Add (e1, e2) when not (is_value e1) -> Add (step e1, e2)
  | Add (v1, e2) -> Add (v1, step e2)
  | Eq (LitInt n1, LitInt n2) -> LitBool (n1 = n2)
  | Eq (e1, e2) when not (is_value e1) -> Eq (step e1, e2)
  | Eq (v1, e2) -> Eq (v1, step e2)
  | e when is_value e -> raise Stuck
  | _ -> raise Stuck

let rec eval_full : type a. a expr -> a expr =
 fun e ->
  try
    let e' = step e in
    eval_full e'
  with
  | Stuck -> e
