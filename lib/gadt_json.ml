type ujson =
  | UStr : string -> ujson
  | UNum : float -> ujson
  | UBool : bool -> ujson
  | UNull : ujson
  | UArr : ujson list -> ujson
