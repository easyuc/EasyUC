(* UcParseFile module interface *)

(* parse a DSL specification *)

open EcParsetree
open UcSpec

type file_or_id =
  | FOID_File of string  (* file name, interpreted relative to working
                            directory, if not fully qualified *)
  | FOID_Id   of psymbol (* root name of .uc file, matching ident from
                            lexer (and so without ".uc" and without "/"s *)

(* second component of result will be the filename of the locations
   of the spec *)

val parse_file_or_id : file_or_id -> spec * string
