(* UcState module interface *)

(* Global state of UC DSL tool *)

(* the precedence of include dirs is from the beginning of the list
   (highest) to the end of the list (lowest)

   this is the *opposite* of the order of the -I options to ucdsl *)

val get_include_dirs : unit -> string list

val set_include_dirs : string list -> unit

(* add to include dirs so as to have highest precedence (i.e., goes in
   the list at the beginning *)

val add_highest_include_dirs : string -> unit

(* add to include dirs so as to have lowest precedence (i.e., goes in
   the list at the end) *)

val add_lowest_include_dirs : string -> unit

val set_raw_messages : unit -> unit

val get_raw_messages : unit -> bool
