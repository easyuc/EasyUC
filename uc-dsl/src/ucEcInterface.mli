(* UcEcInterface module interface *)

(* Interface with EasyCrypt *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
  string EcLocation.located    ->  (* theory *)
  [ `Export | `Import ] option ->  (* should we export/import the theory's
                                      definitions *)
  unit
