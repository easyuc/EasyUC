(* UcParseAndTypecheckFile module *)

(* parse and then typecheck a DSL specification *)

open UcMessage
open UcSpec
open UcParseFile
open UcTypecheck

let parse_and_typecheck_file file =
  let spec = parse_file file in
  try typecheck spec with
  | TypeError (loc, msg) -> error_message loc msg
