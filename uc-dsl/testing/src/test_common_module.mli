(* test_common_module *)
(* This file contains functions which are used by various
other files *)

open Test_types
   
exception Error of string

val print_list : expr list -> unit

(* print_list takes a list of expressions as in input and prints 
each of the expressions in the list. Here expressions are of type
Desc of string or Args of string list or Outcome of outcome * string *)

val check_ec_standard : string -> string
val check_fields : expr list -> string * string
val get_desc : expr list -> string
val read_file : string -> string
val parse : string -> expr list
val walk_directory_tree :
  string -> string list -> string -> string list * string
val run : string -> string array -> int option * string
