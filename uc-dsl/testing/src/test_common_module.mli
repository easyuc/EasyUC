(* test_common_module *)
(* This file contains functions which are used by various
other files *)

open Test_types
open Unix
   

val print_expr : expr -> unit
val print_list : expr list -> unit
val check_ec_standard : string -> string
val get_desc : expr list -> string
val read_file : string -> string
val parse : string -> expr list
val walk_directory_tree :
  string -> string list -> string -> string list * string
val read_to_eof : in_channel -> string
val norm_stat : process_status -> int option
val run : string -> string array -> int option * string
