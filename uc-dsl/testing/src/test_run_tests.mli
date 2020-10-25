(* test_run_tests *)

(* This file contains functions which runs each test
and determines whether a test is a success or fail
and maintains log *)

open Test_types

exception Error of string
val verbose : bool ref
val debug : bool ref
val quiet : bool ref
val log_str : string ref
val sec_str : string ref
val desc_str : string ref
val check_name : string list -> unit
val dir_name : string -> unit
val last_element : 'a array -> 'a list -> 'a array
val match_expr :
  expr list ->
  string array ->
  outcome ->
  string -> int -> string array * outcome * string
val create_conflict : string -> string -> string -> unit
val parse_file : string -> int -> int
val log_fun : unit -> unit
val pre_verbose : string -> 'a
