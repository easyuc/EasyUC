(* UcMessage module interface *)

val error_message : EcLocation.t -> string -> 'a

val warning_message : EcLocation.t -> string -> unit

val non_loc_error_message : string -> 'a

val failure : string -> 'a
