(* ucTypes.ml *)

(* We colapse ty from ecTypes to ty_node and look at only Tconstr,
   Tfun and Ttuple.

   We assume there are no name clashes, and we don't need type paths,
   so EcPath can be colapsed to the last symbol = string.

   Furthermore, we assume that Tconstr of ty_node is applied to at
   most one type, so ty list colapses to option (either empty or one
   element)

   TODO it should be list, since tuples in constructor are
   not single parameter but list :( *)

type typ = 
        | Tconstr of string * typ option
        | Tvar of string
        | Ttuple of typ list

let builtin_type_names = ["port"; "univ"]

let portType = Tconstr ("port", None)

let univType = Tconstr ("univ", None)

let boolType = Tconstr ("bool", None)

let string_of_typ (typ : typ) : string =
  let rec sot tyi s =
    match tyi with
    | Tconstr (sfx, Some tyo) -> sot tyo (s ^ " " ^ sfx)
    | Tconstr (sfx, None)     -> s ^ sfx
    | Tvar sfx                -> s ^ sfx
    | Ttuple tl ->
        "(" ^
        (List.fold_left (fun s t -> s ^ " " ^ (sot t "")) "" tl) ^
        ")" in
  sot typ ""
