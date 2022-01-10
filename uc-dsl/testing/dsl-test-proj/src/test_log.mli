(* Test_log *)

(* This file handles writing, reading logs *)

(* creates a 'log' file in the current working directory *)

val create_log : unit -> unit

(* writes str in the file *)

val write_log : string -> string -> unit
