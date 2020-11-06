(* UcTypes module *)

(* We colapse ty from ecTypes to ty_node and look at only Tconstr,
   Tfun and Ttuple.

   We assume there are no name clashes, and we don't need type paths,
   so EcPath can be colapsed to the last symbol = string.

   Furthermore, we assume that Tconstr of ty_node is applied to at
   most one type, so ty list colapses to option (either empty or one
   element)

   TODO it should be list, since tuples in constructor are
   not single parameter but list :( *)

open Format
open UcMessage
open EcTypes

(*
type typ = 
        | Tconstr of string * typ option
        | Tvar of string
        | Ttuple of typ list

let builtin_type_names = ["port"; "univ"]

let port_type = Tconstr ("port", None)

let univ_type = Tconstr ("univ", None)

let bool_type = Tconstr ("bool", None)

let compatible_types t1 t2 = t1 = t2
*)

(* can a type be formatted in any context with no parentheses *)

let is_basic (typ : ty) =
  match typ.ty_node with
  | Tconstr (_, []) -> true
  | Tvar _            -> true
  | _                 -> false

let rec format_typ (ppf : formatter) (typ : ty) : unit =
  match typ.ty_node with
  | Tconstr (constr, [])  -> fprintf ppf "%s" (EcPath.tostring constr)
  | Tconstr (constr, tyl) ->
      let cstr = EcPath.tostring constr in
      fprintf ppf "@[<hv>%s@ %a@]" cstr format_basic_typ_list tyl
  | Tvar tvar                  -> fprintf ppf "%s" (EcIdent.tostring tvar)
  | Ttuple typs                ->
      let rec fts ppf typs =
        match typs with
        | [typ]       -> format_basic_typ ppf typ
        | typ :: typs ->
            fprintf ppf "@[<hv>%a *@ %a@]" format_basic_typ typ fts typs
        | []          -> failure "cannot happen" in
      fts ppf typs
  | Tunivar tunivar -> fprintf ppf "%i" tunivar
  | Tfun (t1,t2) -> fprintf ppf "@[<hv>%a *@ %a@]" 
     format_basic_typ t1 format_basic_typ t2
  | Tglob tglob -> fprintf ppf "@[<hv>%a@]" EcPath.pp_m tglob

and format_basic_typ (ppf : formatter) (typ : ty) : unit =
  if is_basic typ
  then format_typ ppf typ
  else fprintf ppf "(@[%a@])" format_typ typ

and format_basic_typ_list (ppf : formatter) (tyl : ty list) : unit =
  List.iter (format_basic_typ ppf) tyl
  
