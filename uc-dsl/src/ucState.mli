(* UcState module interface *)

(* Global state of UC DSL tool *)

val get_include_dirs : unit -> string list

val set_include_dirs : string list -> unit

val add_to_include_dirs : string -> unit

val set_raw_messages : unit -> unit

val get_raw_messages : unit -> bool
