(* ucParseAndTypecheckFile.ml *)

(* parse and then typecheck a DSL specification *)

open UcParseFile
open UcTypecheck

let parse_and_typecheck_file ch =
  let spec = parse_file ch in typecheck spec
