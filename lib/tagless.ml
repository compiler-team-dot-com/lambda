module type Symantics = sig
  type ('c, 'dv) repr

  (* *)
  val int : int -> ('c, int) repr
  val bool : bool -> ('c, bool) repr

  (* *)
  val lam : (('c, 'da) repr -> ('c, 'db) repr) -> ('c, 'da -> 'db) repr
  val app : ('c, 'da -> 'db) repr -> ('c, 'da) repr -> ('c, 'db) repr

  (* *)
  val add : ('c, int) repr -> ('c, int) repr -> ('c, int) repr

  val if_ :
    ('c, bool) repr -> (unit -> 'x) -> (unit -> 'x) -> (('c, 'da) repr as 'x)
end

module Example (S : Symantics) = struct
  open S

  let test1 () = app (lam (fun x -> x)) (bool true)
end

(* R evaluates an object term to its value in the metalanguage. *)
module R : Symantics with type ('c, 'dv) repr = 'dv = struct
  type ('c, 'dv) repr = 'dv

  let int (x : int) = x
  let bool (b : bool) = b
  let lam f = f
  let app e1 e2 = e1 e2
  let add e1 e2 = e1 + e2
  let if_ eb et ee = if eb then et () else ee ()
end

(* L measures the length of each object term. *)
module L : Symantics with type ('c, 'dv) repr = int = struct
  type ('c, 'dv) repr = int

  let int (_ : int) = 1
  let bool (_ : bool) = 1
  let lam f = f 0 + 1
  let app e1 e2 = e1 + e2 + 1
  let add e1 e2 = e1 + e2 + 1
  let if_ eb et ee = eb + et () + ee () + 1
end

module C : Symantics with type ('c, 'dv) repr = 'dv code = struct
  type ('c, 'dv) repr = 'dv code

  let int (x:int) = .<x>.
  let bool (b:bool) = .<b>.
  let lam f = .<fun x -> .~(f .<x>.)>.
  let app e1 e2 = .<.~e1 .~e2>.
  let fix f = .<let rec self n = .~(f .<self>.) n in self>.
  let add e1 e2 = .<.~e1 + .~e2>.
  let mul e1 e2 = .<.~e1 * .~e2>.
  let leq e1 e2 = .<.~e1 <= .~e2>.
  let if_ eb et ee = .<if .~eb then .~(et ()) else .~(ee ())>.
end

let () =
  let module ExR = Example (R) in
  let value = ExR.test1 () in
  let _ = Printf.printf "Eval: %b\n" value in

  let module ExL = Example (L) in
  let value = ExL.test1 () in
  let _ = Printf.printf "Eval: %d\n" value in

  let open Runcode in

  let module ExC = Example (C) in
  let value = ExC.test1 () in
  let _ = Printf.printf "Eval: %b\n" (run value) in
  ()
