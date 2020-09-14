(* UcParseAndTypecheckFile module interface *)

(* Parse and then typecheck a DSL specification *)

open UcParseFile
open UcTypedSpec

val parse_and_typecheck_file_or_id : file_or_id -> typed_spec
