(* test_main *)

(*this is where the test suite's main file *)

val dirs_list : string list ref
val check_dirs : string -> int
val verify_dir : string -> string
val pre_debug : string -> 'a
val call_dir_test : string list -> 'a
val usage_msg : string
val main : 'a
