(* UcParseFile module interface *)

(* Parse a DSL specification *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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

(* second component of result will be the filename of the locations
   of the spec *)

val parse_file_or_id : file_or_id -> spec * string
