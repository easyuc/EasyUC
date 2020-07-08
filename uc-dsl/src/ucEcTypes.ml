(* UcEcTypes module *)

open UcTypes
open UcSpec
open EcLocation

let check_named_type (tyname : id) : typ =
  let tyn = unloc tyname in
  try ignore (List.find (fun tyn' -> tyn' = tyn) builtin_type_names);
      Tconstr (tyn, None) with
    Not_found ->
      if UcEcInterface.exists_type tyn then Tconstr (tyn, None)
      else parse_error (loc tyname) (Some ("Non-existing type: " ^ tyn))

let rec check_type (ty : ty) : typ =
  match ty with
  | NamedTy id -> check_named_type id
  | TupleTy tl -> Ttuple (List.map (fun t -> check_type t) tl)
