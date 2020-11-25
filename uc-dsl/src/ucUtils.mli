(* UcUtils module interface *)

(* UC DSL Utilities *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open Batteries
open EcLocation

val find_dup : ?cmp:('a -> 'a -> int) -> 'a list -> 'a option

val has_dup  : ?cmp:('a -> 'a -> int) -> 'a list -> bool

val index_of_ex : 'a -> 'a list -> int

val filename_of_loc : EcLocation.t -> string

val mergelocs : 'a located list -> EcLocation.t

val dummyloc : 'a -> 'a located

val dummylocl : 'a list -> 'a located list

val string_of_id_path : string list -> string

val format_strings : Format.formatter -> char -> string list -> unit

val format_strings_comma : Format.formatter -> string list -> unit

val format_id_paths_comma : Format.formatter -> string list list -> unit

val sl1_starts_with_sl2 : string list -> string list -> bool

val capitalized_root_of_filename_with_extension : string -> string

(* find_file root ext prelude_dir include_dirs

   searches for root concatenated with ext, or failing that the result
   of capitalizing the first letter of root concatenated with ext:

   we first look in the directory prelude, then in the current
   directory, and finally in the include dirs (from front (highest
   precedence) to back (lowest precedence)) *)

val find_file : string -> string -> string -> string list -> string option
  
