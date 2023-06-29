(* UcEcInterface module interface *)

(* Interface with EasyCrypt *)

(* initialize EasyCrypt *)

val init : unit -> unit

(* return the environment of the current scope *)

val env : unit -> EcEnv.env

(* require an EasyCrypt theory *)

val require :
  string EcLocation.located    ->  (* theory *)
  [ `Export | `Import ] option ->  (* should we export/import the theory's
                                      definitions *)
  unit
