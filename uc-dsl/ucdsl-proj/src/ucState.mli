(* UcState module interface *)

(* Global State of UC DSL tool *)

(* include dirs list

   the precedence of include dirs is from the beginning of the list
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

(* boolean saying whether messages should be issued in raw format,
   for consumption, e.g., by Emacs major mode for UC DSL

   default is non-raw messages, intended to be read by humans *)

val set_raw_messages : unit -> unit

val get_raw_messages : unit -> bool

(* boolean saying whether top-level defintions should be required to
   be grouped into units

   default is that grouping into units is not required *)

val set_units : unit -> unit

val get_units : unit -> bool
