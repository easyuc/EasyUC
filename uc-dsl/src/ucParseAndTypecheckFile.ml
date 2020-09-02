(* UcParseAndTypecheckFile module *)

(* parse and then typecheck a DSL specification *)

open UcParseFile
open UcTypecheck

let parse_and_typecheck_file file =
  let spec = parse_file file in
  typecheck spec
