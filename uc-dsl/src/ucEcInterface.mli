(* UcEcInterface module interface *)

(* Interface with EasyCrypt *)

open UcTypes

val init : unit -> unit

val env : unit -> EcEnv.env

val require :
  string EcLocation.located -> [ `Export | `Import ] option -> unit

val exists_type : string -> bool

val exists_operator : string -> bool

val get_operator_sig : string -> typ * typ list
