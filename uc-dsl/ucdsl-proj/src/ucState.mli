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

(*** only one of the next two options, raw_messages and pg_mode, should
     be set ***)

(* boolean saying whether messages should be issued in raw format
   for consumption by Emacs major mode for UC DSL

   default is non-raw messages, intended to be read by humans

   should only be set when a .uc file is being processed *)

val set_raw_messages : unit -> unit

val unset_raw_messages : unit -> unit

val get_raw_messages : unit -> bool

(* pg_mode tells the EcMessages to display errors in a format suitable
   for Proof General. The pg_start_position is set to the end of the
   standard input buffer each time an interpreter command is
   processed, in order to allow proper highlighting of error location
   in ProofGeneral's script buffer.

   the default is false, but it will be set iff the interpreter is
   running and taking its input from the standard input (not a .uci
   file) *)   

val set_pg_mode : unit -> unit

val unset_pg_mode : unit -> unit

val get_pg_mode : unit -> bool

val set_pg_start_pos : int -> unit

val get_pg_start_pos : unit -> int

(* boolean saying whether the interpreter should be run in batch mode,
   where output (except debugging output, if selected) is limited to
   only error messages (which terminate execution with exit status 1),
   and if there are no error message the exit status is 0

   default is no batch mode

   may optionally be set when the interpreter is running on a .uci file *)

val set_batch_mode : unit -> unit

val get_batch_mode : unit -> bool

(* boolean saying whether interpreter debugging output should be
   generated and printed

   default is no debugging messages, and should only be set if
   the interpreter is running *)

val set_debugging : unit -> unit

val unset_debugging : unit -> unit

val get_debugging : unit -> bool

(* boolean saying whether top-level definitions should be required to
   be grouped into units

   default is that grouping into units is not required, but it is
   set by the interpreter *)

val set_units : unit -> unit

val get_units : unit -> bool
