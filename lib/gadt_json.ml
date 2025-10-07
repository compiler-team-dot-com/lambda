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

(* Building typed JSON from untyped JSON using existentials *)
type etjson = ETJson : 'a tjson -> etjson
type etarr = ETArr : 'a tarr -> etarr

let rec tjson_of_ujson : ujson -> etjson = function
  | UStr s -> ETJson (Str s)
  | UNum n -> ETJson (Num n)
  | UBool b -> ETJson (Bool b)
  | UNull -> ETJson Null
  | UArr arr ->
      let (ETArr arr') = tarr_of_uarr arr in
      ETJson (Arr arr')

and tarr_of_uarr : ujson list -> etarr = function
  | [] -> ETArr Nil
  | j :: js ->
      let (ETJson j') = tjson_of_ujson j in
      let (ETArr js') = tarr_of_uarr js in
      ETArr (j' :: js')
