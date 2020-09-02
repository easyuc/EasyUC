(* UcMessage module interface *)

open Format

val error_message : EcLocation.t -> (formatter -> unit) -> 'a

val warning_message : EcLocation.t -> (formatter -> unit) -> unit

val non_loc_error_message : (formatter -> unit) -> 'a

val failure : string -> 'a
