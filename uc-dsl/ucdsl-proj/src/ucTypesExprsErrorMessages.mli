(* UcTypesExprsErrorMessages module interface *)

(* Formatting error messages issued when translating types and
   expressions *)

(* adapted from ecUserMessages.mli of EasyCrypt distribution *)

open EcEnv
open UcTransTypesExprs

val pp_tyerror : env -> Format.formatter -> tyerror -> unit
