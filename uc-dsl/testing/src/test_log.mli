(* Test_log *)

(* This file handles writing, reading logs *)

val create_log : unit -> unit
(* creates a 'log' file in the current working directory *)
  
val write_log : string -> string -> unit

(* write_log : file -> str -> unit
wites str in the file
 *)
