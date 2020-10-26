(* UcEcInterface module interface *)

(* Interface with EasyCrypt *)

open UcTypes

(* initialize EasyCrypt *)

val init : unit -> unit

(* EasyCrypt critical errors cause termination with an error message,
   but EasyCrypt warnings are collected in a list, which may be retrieved
   or reset *)

val get_ec_warnings : unit -> string list

val reset_ec_warnings : unit -> unit

(* return the environment of the current scope *)

val env : unit -> EcEnv.env

(* require an EasyCrypt theory *)

val require :
  string EcLocation.located -> [ `Export | `Import ] option -> unit

val exists_type : string -> bool

val exists_operator : string -> bool

val get_operator_sig : string -> typ * typ list