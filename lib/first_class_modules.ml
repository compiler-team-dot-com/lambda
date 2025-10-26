module type S = sig
  type t

  val show : t -> string
end

(* A module implementing S *)
module IntShow = struct
  type t = int

  let show = string_of_int
end

(* Turn it into an ordinary value *)
type int_show = (module S with type t = int)

let show_any : type a. (module S with type t = a) -> a -> string =
 fun m x ->
  let module M = (val m) in
  M.show x

let show_int : int_show -> int -> string = fun (module S) n -> S.show n

let _ =
  print_endline @@ show_any (module IntShow) 3;
  print_endline @@ show_int (module IntShow) 3;
  let is : int_show = (module IntShow) in
  print_endline @@ show_any is 3;
  print_endline @@ show_int is 3

let m : (module S with type t = int) = (module IntShow : S with type t = int)

let use_explicit () =
  let module M = (val m : S with type t = int) in
  print_endline (M.show 42)

let use_pattern () =
  let (module M : S with type t = int) = m in
  print_endline (M.show 99)

let () =
  use_explicit ();
  use_pattern ()
