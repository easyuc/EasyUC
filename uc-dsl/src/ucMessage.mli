(* UcMessage module interface *)

val error_message : string -> EcLocation.t option -> string -> 'a

val warning_message : string -> EcLocation.t option -> string -> unit
