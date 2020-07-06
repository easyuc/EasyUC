(* ucParseFile.mli *)

(* parse a DSL specification *)

open UcSpec

val parse_file : in_channel -> spec
