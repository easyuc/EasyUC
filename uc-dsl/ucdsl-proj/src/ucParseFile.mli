(* UcParseFile module interface *)

(* Parse a DSL specification *)

open EcSymbols
open EcLocation
open UcSpec

type file_or_id =
  (* file name, interpreted relative to working directory, if not
      fully qualified *)
  | FOID_File of string
  (* root name of .uc file, initial letter capitalized, and without
     ".uc" and without "/"s, normally located in file that was lexed *)
  | FOID_Id   of symbol located

(* parse and then typecheck a file_or_id describing a .uc file

   second component of result will be the qualified name of the .uc
   file *)

val parse_file_or_id : file_or_id -> spec * string
