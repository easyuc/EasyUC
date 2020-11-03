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
  Test_types.expr list ->
  string array ->
  Test_types.outcome ->
  string -> string array * Test_types.outcome * string
val create_conflict : string -> string -> string -> unit
val parse_file : string -> int -> int
val log_fun : unit -> unit
val pre_verbose : string -> 'a
