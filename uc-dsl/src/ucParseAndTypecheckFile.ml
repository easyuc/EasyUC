(* UcParseAndTypecheckFile module *)

(* parse and then typecheck a DSL specification *)

open UcParseFile
open UcTypecheck

let parse_and_typecheck_file_or_id foid =
  let spec = parse_file_or_id foid in
  typecheck spec
