(* Well-typed representations *)

type ('e, 'a) idx =
  | Zero : ('e * 'a, 'a) idx
  | Succ : ('e, 'a) idx -> ('e * 'b, 'a) idx

type ('e, 'a) texp =
  | Var : ('e, 'a) idx -> ('e, 'a) texp
  | Lam : ('e * 'a, 'b) texp -> ('e, 'a -> 'b) texp
  | App : ('e, 'a -> 'b) texp * ('e, 'a) texp -> ('e, 'b) texp

let example = Lam (Lam (Var (Succ Zero)))

(* Untyped representations *)

type uty =
  | Unit
  | Arr of uty * uty

type uexp =
  | Var of int
  | Lam of uty * uexp
  | App of uexp * uexp

(* Singleton types to express type-checking *)

type 'a ty =
  | Unit : unit ty
  | Arr : 'a ty * 'b ty -> ('a -> 'b) ty

type 'e env =
  | Empty : unit env
  | Cons : 'e env * 'a ty -> ('e * 'a) env

(* Existential types *)

type some_ty = Ty : 'a ty -> some_ty
type 'e some_idx = Idx : 'a ty * ('e, 'a) idx -> 'e some_idx
type 'e some_texp = Exp : 'a ty * ('e, 'a) texp -> 'e some_texp

(* Dynamic type equality check *)

type (_, _) eq = Refl : ('a, 'a) eq

exception Clash

let rec eq_ty : type a b. a ty -> b ty -> (a, b) eq =
 fun ta tb ->
  match (ta, tb) with
  | Unit, Unit -> Refl
  | Unit, Arr _ | Arr _, Unit -> raise Clash
  | Arr (ta1, ta2), Arr (tb1, tb2) ->
      let Refl = eq_ty ta1 tb1 in
      let Refl = eq_ty ta2 tb2 in
      Refl

(* "Checking" a type (no failure) *)

let rec check_ty : uty -> some_ty = function
  | Unit -> Ty Unit
  | Arr (ta, tb) ->
      let (Ty ta) = check_ty ta in
      let (Ty tb) = check_ty tb in
      Ty (Arr (ta, tb))

(* "Checking" a variable *)

exception Ill_scoped

let rec check_var : type e. e env -> int -> e some_idx =
 fun env n ->
  match env with
  | Empty -> raise Ill_scoped
  | Cons (env, ty) ->
      if n = 0 then Idx (ty, Zero)
      else
        let (Idx (tyn, idx)) = check_var env (n - 1) in
        Idx (tyn, Succ idx)

(* "Checking" an input expression *)

exception Ill_typed

let rec check : type a e. e env -> uexp -> e some_texp =
 fun env exp ->
  match exp with
  | Var n ->
      let (Idx (ty, idx)) = check_var env n in
      Exp (ty, Var idx)
  | Lam (tya, exp') ->
      let (Ty tya) = check_ty tya in
      let (Exp (tyb, exp')) = check (Cons (env, tya)) exp' in
      Exp (Arr (tya, tyb), Lam exp')
  | App (exp_f, exp_arg) ->
      let (Exp (ty_f, exp_f)) = check env exp_f in
      let (Exp (ty_arg, exp_arg)) = check env exp_arg in
      begin
        match ty_f with
        | Arr (ty_arg', ty_res) ->
            let Refl = eq_ty ty_arg ty_arg' in
            Exp (ty_res, App (exp_f, exp_arg))
        | _ -> raise Ill_typed
      end
