(* Introduction to tagless-final and
  optimizations (normalization) with the tagless-final approach
*)

(* The simplest DSL *)
module type SYM = sig
  type 'a repr

  val int : int -> int repr
  val add : int repr -> int repr -> int repr
end

(* We already can write sample expressions;
   I will stand for `interpreter', an instance of SYM *)
module Ex1 (I : SYM) = struct
  open I

  let res = add (int 1) (int 2)
end

module Ex2 (I : SYM) = struct
  open I

  let res = add (add (int 1) (int 2)) (add (int 3) (int 4))
end

module Ex3 (I : SYM) = struct
  open I

  let res = add (add (int 3) (add (int 5) (int 0))) (add (int 1) (int 0))
end

(* Its two interpreters *)

(* The meta-circular interpreter *)
module Ru = struct
  type 'a repr = 'a

  let int x = x
  let add = ( + )
end
(* We can evaluate the examples *)

let[@warning "-8"] 3 =
  let module M = Ex1 (Ru) in
  M.res

let[@warning "-8"] 10 =
  let module M = Ex2 (Ru) in
  M.res

(* The Show interpreter, which interprets every expression to a string *)
module Sh = struct
  type 'a repr = string

  let int = string_of_int
  let add x y = "(" ^ x ^ " + " ^ y ^ ")"
end

let[@warning "-8"] "(1 + 2)" =
  let module M = Ex1 (Sh) in
  M.res

let[@warning "-8"] "((1 + 2) + (3 + 4))" =
  let module M = Ex2 (Sh) in
  M.res

(* Let us transform the expression to its negation.
   A transformer can also be written as an interpreter.
*)

module Neg (From : SYM) = struct
  type 'a repr = 'a From.repr

  let int x = From.int (-x)
  let add e1 e2 = From.add e1 e2
end

(* Neg interprets the DSL in terms of another interpreter, From.
On the surface of it, Neg is the interpreter transformer. Dually,
it can also be viewed as the transformer of an DSL expression:
*)

module Ex2Neg (F : SYM) = Ex2 (Neg (F))

(* Here Ex2Neg is a new, negated DSL expression.
   We can interpret it just like any other expression, like Ex2 *)

let[@warning "-8"] -10 =
  let module M = Ex2Neg (Ru) in
  M.res

let[@warning "-8"] "((-1 + -2) + (-3 + -4))" =
  let module M = Ex2Neg (Sh) in
  M.res

let[@warning "-8"] 10 =
  let module Ex2NegNeg (F : SYM) = Ex2Neg (Neg (F)) in
  let module M = Ex2NegNeg (Ru) in
  M.res

(* Before getting to the optimization framework, let us see
   a simple optimization outside the framework. The approach we
   describe is not ad hoc -- it is in fact the general approach
   of Partial Evaluation.

The optimization is not easily extensible and a bit harder to
combine with others. Our framework eliminates these drawbacks. We
re-implement this optimization in our framework later on.
*)

(* The optimization is suppressing additions to zero.
   That is, we implement the rules
   0 + x --> 0
   x + 0 --> 0
We assume for simplicity that all integer literals are non-negative.
It is an exercise to the reader to remove that assumption.
*)

module SuppressZeroPE (F : SYM) = struct
  type 'a repr = {
    dynamic : 'a F.repr;
    known_zero : bool;
  }

  let int x = { dynamic = F.int x; known_zero = x = 0 }

  let add e1 e2 =
    match (e1, e2) with
    | { known_zero = true; _ }, x -> x
    | x, { known_zero = true; _ } -> x
    | { dynamic = x; _ }, { dynamic = y; _ } ->
        { dynamic = F.add x y; known_zero = false }
end

let[@warning "-8"] "((3 + 5) + 1)" =
  let module Ex3NoZerosPE (F : SYM) = Ex3 (SuppressZeroPE (F)) in
  let module M = Ex3NoZerosPE (Sh) in
  M.res.dynamic

(*
- : int SuppressZeroPE(Sh).repr =
{SuppressZeroPE(Sh).dynamic = "((3 + 5) + 1)"; known_zero = false}
*)

(* ------------------------------------------------------------------------
 * Optimization framework
 *)

(*
The key to tagless-final transformations is that an interpreter, the
instance of SYM, can be interpreting in terms of another interpreter.

*)

(* A bit of infrastructure. Let's extend SYM with the observation type and
the observation function. Think of that as the `run' operation in a monad.
*)

module type SYMOBS = sig
  include SYM

  type 'a obs

  val observe : 'a repr -> 'a obs
end

(* We can trivially add observe to our Ru and Sh interpreters *)
module AddObs (I : SYM) = struct
  include I

  type 'a obs = 'a repr

  let observe x = x
end

(* Before we start the transformations, let's define a connection between
   two types 'a from and 'a term
*)

module type Trans = sig
  type 'a from
  type 'a term

  val fwd : 'a from -> 'a term (* reflection  *)
  val bwd : 'a term -> 'a from (* reification *)
end

(* Generally speaking, this is not a bijection: fwd is generally not
surjective and bwd is not injective. The operation fwd is akin to
concretization and bwd to abstraction, abstracting away the working data
used during the optimization.
*)

(* The default, generic optimizer
   Concrete optimizers are built by overriding the interpretations
   of some DSL forms.
*)
module SYMT (X : Trans) (F : SYMOBS with type 'a repr = 'a X.from) = struct
  open X

  type 'a repr = 'a term
  type 'a obs = 'a F.obs

  let int x = fwd (F.int x)
  let add x y = fwd (F.add (bwd x) (bwd y))
  let observe x = F.observe (bwd x)
end

module IdentityPass (F : SYM) = struct
  module X = struct
    type 'a from = 'a F.repr
    type 'a term = 'a from

    let fwd x = x
    let bwd x = x
  end

  module IDelta = struct end
end

module Identity (F : SYMOBS) = struct
  module OptM = IdentityPass (F)
  include SYMT (OptM.X) (F)
  include OptM.IDelta
end

module IdentitySh = Identity (AddObs (Sh))

let[@warning "-8"] "((3 + (5 + 0)) + (1 + 0))" =
  let module M = Ex3 (IdentitySh) in
  IdentitySh.observe M.res

(* Now we redo the optimization within the framework:
   define the interpreter that will override SYMT with
   optimization-specific transformations
   The following functor is the container for two modules: X describes
   the reflection/reification and IDelta describes the optimizations
   themselves, as interpretations of only those expression forms
   the DSL that are affected by this particular optimization.

As Dybjer and Filinski write, reflection (fwd) is a wrapper, injecting
the opaque value into |'a term|.
*)
module SuppressZeroPass (F : SYM) = struct
  module X = struct
    type 'a from = 'a F.repr
    (* Each optimization has its own term type suitable for it.
           *)

    type ann =
      | Zero
      | Unk

    type 'a term = ann * 'a from

    let fwd x = (Unk, x) (* generic reflect *)
    let bwd (_, x) = x
  end

  open X

  module IDelta = struct
    (* Now, the optimization is programmed as overriding int and add
         to perform non-standard evaluation.
         We need to override only those interpreter functions that
         participate in optimization. In our case, there are only two
         altogether, and they all participate in the optimization.
       *)
    let int n = ((if n = 0 then Zero else Unk), F.int n)

    let add : int term -> int term -> int term =
     fun x y ->
      match (x, y) with
      | (Zero, _), x -> x
      | x, (Zero, _) -> x
      | (Unk, x), (Unk, y) -> (Unk, F.add x y)
  end
end

(* Combine the optimization with the base interpreter
   (well, the base interpreter is so simple that the interpretation
   overrides everything in it. But we get to more complex interpreters
   at the end.)
*)
module SuppressZero (F : SYMOBS) = struct
  module OptM = SuppressZeroPass (F)
  include SYMT (OptM.X) (F)
  include OptM.IDelta (* overriding int and add in SYMT *)
end

module SuppressZeroSh = SuppressZero (AddObs (Sh))

let[@warning "-8"] "(1 + 2)" =
  let module M = Ex1 (SuppressZeroSh) in
  SuppressZeroSh.observe M.res

let[@warning "-8"] "((3 + 5) + 1)" =
  let module M = Ex3 (SuppressZeroSh) in
  SuppressZeroSh.observe M.res

(* Let's now do another transformation (optimization) --
  transform the add expression into the `normal', that is,
  linearized form: (add 1 (add 2 ...)):
   linear_expr ::= int | add int linear_expr
Expressions in this form can be compiled to a sequence of simple
addition instructions over a single accumulator (think of Z80).
*)

module LinearizeAddPass (F : SYM) = struct
  module X = struct
    type 'a from = 'a F.repr
    (* This is not a recursive type ! *)

    type ann =
      | Add of (int from -> int from) * int from
      | Unk

    type 'a term = ann * 'a from

    let fwd x = (Unk, x) (* generic reflect *)
    let bwd (_, x) = x
  end

  open X

  module IDelta = struct
    (* Now, the optimization is programmed as overriding int and add
         to perform non-standard evaluation.
         We need to override only those interpreter functions that
         participate in optimization. In our case, there are only two
         altogether, and they all participate in the optimization.
       *)
    (* On proving correctness:
      Theorem: if e : int term, then e represents a linearized addition
      expression. Proof: by induction.
    *)
    (* Base case. *)
    let int n = (Add ((fun x -> x), F.int n), F.int n)

    (* Induction case. By induction hypotheses, the arguments of add
      are linearized.
    *)
    let add : int term -> int term -> int term =
     fun x y ->
      match (fst x, fst y) with
      | Add (fx, nx), Add (fy, ny) ->
          let adder = fun nil -> fx (F.add nx (fy nil)) in
          (Add (adder, ny), adder ny)
      | Unk, Add (fy, ny) ->
          let adder = fun nil -> F.add (snd x) (fy nil) in
          (Add (adder, ny), adder ny)
      | Add (fx, nx), Unk ->
          let adder = fun nil -> fx (F.add nx nil) in
          (Add (adder, snd y), adder (snd y))
      | _ -> (Unk, F.add (bwd x) (bwd y))
  end
end

module LinearizeAdd (F : SYMOBS) = struct
  module OptM = LinearizeAddPass (F)
  include SYMT (OptM.X) (F)
  include OptM.IDelta
end

(* Let see the results *)
module SLin = LinearizeAdd (AddObs (Sh))

let[@warning "-8"] "(1 + 2)" =
  let module M = Ex1 (SLin) in
  SLin.observe M.res

let[@warning "-8"] "(1 + (2 + (3 + 4)))" =
  let module M = Ex2 (SLin) in
  SLin.observe M.res

let[@warning "-8"] "(3 + (5 + (0 + (1 + 0))))" =
  let module M = Ex3 (SLin) in
  SLin.observe M.res

(* For these optimizations, we can compose in either order *)
module SLinZero = SuppressZero (SLin)

let[@warning "-8"] "(1 + 2)" =
  let module M = Ex1 (SLinZero) in
  SLinZero.observe M.res

let[@warning "-8"] "(1 + (2 + (3 + 4)))" =
  let module M = Ex2 (SLinZero) in
  SLinZero.observe M.res

let[@warning "-8"] "(3 + (5 + 1))" =
  let module M = Ex3 (SLinZero) in
  SLinZero.observe M.res

(* Extension *)

(* Let us extend the DSL with first-class functions *)

module type SYMHO = sig
  include SYMOBS

  val lam : ('a repr -> 'b repr) -> ('a -> 'b) repr
  val app : ('a -> 'b) repr -> 'a repr -> 'b repr
end

module Ex4 (I : SYMHO) = struct
  open I

  let res =
    observe @@ lam
    @@ fun x -> add (add x (add (int 5) (int 0))) (add (int 1) (int 0))
end

module Ex5 (I : SYMHO) = struct
  open I

  let res =
    observe @@ lam
    @@ fun x ->
    add
      (add x (add (int 5) (int 0)))
      (add
         (add (add (int 1) (int 0)) (int 7))
         (add (app (lam (fun y -> y)) (int 4)) (int 2)))
end

module RuHO = struct
  include AddObs (Ru)

  let lam f = f
  let app f x = f x
end

(* Old expressions can be interpreted with the new interpreter *)
let[@warning "-8"] 10 =
  let module M = Ex2 (RuHO) in
  M.res

let[@warning "-8"] 9 =
  let module M = Ex4 (RuHO) in
  M.res 3

let[@warning "-8"] 25 =
  let module M = Ex5 (RuHO) in
  M.res 6

(* We write ShHO from scratch, to make the printing prettier
and suppress useless parentheses
*)
module ShHO : SYMHO with type 'a obs = string = struct
  type varcount = int
  type precedence = int
  type 'a repr = precedence -> varcount -> string
  type 'a obs = string

  let observe x = x 0 0
  let paren = function true -> fun x -> "(" ^ x ^ ")" | _ -> fun x -> x
  let varnames = "xyzuvw"

  let varname = function
    | i when i < String.length varnames -> String.make 1 @@ varnames.[i]
    | i -> "x" ^ string_of_int i

  let int = function
    | n when n >= 0 -> fun _ _ -> string_of_int n
    | n -> fun p _ -> paren (p > 10) @@ string_of_int n

  let add x y = fun p i -> paren (p > 3) @@ x 4 i ^ " + " ^ y 4 i
  let app f x = fun p i -> paren (p > 10) @@ f 10 i ^ " " ^ x 11 i

  let lam f =
   fun p i ->
    let v = varname i in
    let body = f (fun _ _ -> v) 0 (i + 1) in
    paren (p > 0) ("L" ^ v ^ ". " ^ body)
end

let[@warning "-8"] "(1 + 2) + (3 + 4)" =
  let module M = Ex2 (ShHO) in
  ShHO.observe M.res

let[@warning "-8"] "Lx. (x + (5 + 0)) + (1 + 0)" =
  let module M = Ex4 (ShHO) in
  M.res

let[@warning "-8"] "Lx. (x + (5 + 0)) + (((1 + 0) + 7) + ((Ly. y) 4 + 2))" =
  let module M = Ex5 (ShHO) in
  M.res

module SYMTHO (X : Trans) (F : SYMHO with type 'a repr = 'a X.from) = struct
  open X
  include SYMT (X) (F)

  let app x y = fwd (F.app (bwd x) (bwd y))
  let lam f = fwd (F.lam (fun x -> bwd (f (fwd x))))
end

module SuppressZeroHO (F : SYMHO) = struct
  module OptM = SuppressZeroPass (F) (* reusing SuppressZeroPass as it was *)
  include SYMTHO (OptM.X) (F)
  include OptM.IDelta
end

module SuppressZeroHOSh = SuppressZeroHO (ShHO)

let[@warning "-8"] "(3 + 5) + 1" =
  let module M = Ex3 (SuppressZeroHOSh) in
  SuppressZeroHOSh.observe M.res

let[@warning "-8"] "Lx. (x + 5) + 1" =
  let module M = Ex4 (SuppressZeroHOSh) in
  M.res

let[@warning "-8"] "Lx. (x + 5) + ((1 + 7) + ((Ly. y) 4 + 2))" =
  let module M = Ex5 (SuppressZeroHOSh) in
  M.res

module LinearizeAddHO (F : SYMHO) = struct
  module OptM = LinearizeAddPass (F)
  include SYMTHO (OptM.X) (F)
  include OptM.IDelta
end

module SLinZeroHO = LinearizeAddHO (SuppressZeroHOSh)

let[@warning "-8"] "3 + (5 + 1)" =
  let module M = Ex3 (SLinZeroHO) in
  SLinZeroHO.observe M.res

let[@warning "-8"] "Lx. x + (5 + 1)" =
  let module M = Ex4 (SLinZeroHO) in
  M.res

let[@warning "-8"] "Lx. x + (5 + (1 + (7 + ((Ly. y) 4 + 2))))" =
  let module M = Ex5 (SLinZeroHO) in
  M.res

let () = print_endline "\nAll Done\n"
