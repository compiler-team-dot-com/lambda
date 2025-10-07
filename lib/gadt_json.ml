type ujson =
  | UStr : string -> ujson
  | UNum : float -> ujson
  | UBool : bool -> ujson
  | UNull : ujson
  | UArr : ujson list -> ujson

type _ tjson =
  | Str : string -> string tjson
  | Num : float -> float tjson
  | Bool : bool -> bool tjson
  | Null : unit tjson
  | Arr : 'a tarr -> 'a tjson

and _ tarr =
  | Nil : unit tarr
  | ( :: ) : 'a tjson * 'b tarr -> ('a * 'b) tarr
