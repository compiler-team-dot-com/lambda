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

type _ tyjson =
  | TyStr : string tyjson
  | TyNum : float tyjson
  | TyBool : bool tyjson
  | TyNull : 'a tyjson -> 'a option tyjson
  | TyArr : 'a tyarr -> 'a tyjson

and _ tyarr =
  | TyNil : unit tyarr
  | ( :: ) : 'a tyjson * 'b tyarr -> ('a * 'b) tyarr

let _ =
  ( TyArr
      (TyStr :: TyBool :: TyNum
      :: TyArr (TyArr (TyStr :: TyNil) :: TyNull TyBool :: TyNil)
      :: TyNil),
    ("one", (true, (3.4, ((("four", ()), (None, ())), ())))) )

(* The negate function, entangled *)
let rec negate : type a. a tjson -> a tjson = function
  | Bool b -> Bool (not b)
  | Arr arr -> Arr (negate_arr arr)
  | v -> v

and negate_arr : type a. a tarr -> a tarr = function
  | Nil -> Nil
  | j :: js -> negate j :: negate_arr js

(* The negate function, disentangled *)
let rec negateD : type a. a tyjson -> a -> a =
 fun t v ->
  match (t, v) with
  | TyBool, true -> false
  | TyBool, false -> true
  | TyArr a, arr -> negate_arrD a arr
  | TyNull j, Some v -> Some (negateD j v)
  | TyNull _, None -> None
  | _, v -> v

and negate_arrD : type a. a tyarr -> a -> a =
 fun t v ->
  match (t, v) with
  | TyNil, () -> ()
  | j :: js, (a, b) -> (negateD j a, negate_arrD js b)

let _ =
  negateD
    (TyArr
       (TyStr :: TyBool :: TyNum
       :: TyArr (TyArr (TyStr :: TyNil) :: TyNull TyBool :: TyNil)
       :: TyNil))
    ("one", (true, (3.4, ((("four", ()), (None, ())), ()))))

(* The negate function, disentangled and "staged" *)
let id x = x
let map_option f = function None -> None | Some x -> Some (f x)

let rec negateDS : type a. a tyjson -> a -> a = function
  | TyBool -> not
  | TyArr a -> negate_arrDS a
  | TyNull j -> map_option (negateDS j)
  | _ -> id

and negate_arrDS : type a. a tyarr -> a -> a = function
  | TyNil -> id
  | j :: js ->
      let n = negateDS j in
      let ns = negate_arrDS js in
      fun (a, b) -> (n a, ns b)

let _ =
  let staged =
    negateDS
      (TyArr
         (TyStr :: TyBool :: TyNum
         :: TyArr (TyArr (TyStr :: TyNil) :: TyNull TyBool :: TyNil)
         :: TyNil))
  in
  staged ("one", (true, (3.4, ((("four", ()), (None, ())), ()))))

(* Argument: It is typically easier to verify that data matches a particular shape
             than to determine the shape of arbitrary data. *)

let rec unpack_ujson : type a. a tyjson -> ujson -> a option =
 fun ty v ->
  match (ty, v) with
  | TyStr, UStr s -> Some s
  | TyNum, UNum u -> Some u
  | TyBool, UBool b -> Some b
  | TyNull _, UNull -> Some None
  | TyNull j, v -> (
      match unpack_ujson j v with Some v -> Some (Some v) | None -> None)
  | TyArr a, UArr arr -> unpack_uarr a arr
  | _ -> None

and unpack_uarr : type a. a tyarr -> ujson list -> a option =
 fun ty v ->
  match (ty, v) with
  | TyNil, [] -> Some ()
  | j :: js, v :: vs -> (
      match (unpack_ujson j v, unpack_uarr js vs) with
      | Some v', Some vs' -> Some (v', vs')
      | _ -> None)
  | _ -> None

(* With type refinement we learn about types by inspecting values.
   Predicates should return useful evidence rather than true of false. *)
