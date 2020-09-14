(* UcParseFile module interface *)

(* parse a DSL specification *)

open UcSpec

type file_or_id =
  | FOIDFile of string
  | FOIDId   of id

val parse_file_or_id : file_or_id -> spec
