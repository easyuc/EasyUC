(* UcParseAndTypecheckFile module interface *)

(* Parse and then typecheck a DSL specification *)

open UcTypedSpec

val parse_and_typecheck_file : string -> typed_spec
