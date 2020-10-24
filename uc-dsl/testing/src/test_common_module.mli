val print_expr : Test_types.expr -> unit
val print_list : Test_types.expr list -> unit
val check_ec_standard : string -> string
val get_desc : Test_types.expr list -> string
val read_file : string -> string
val parse : string -> Test_types.expr list
val walk_directory_tree :
  string -> string list -> string -> string list * string
val read_to_eof : in_channel -> string
val norm_stat : Unix.process_status -> int option
val run : string -> string array -> int option * string
