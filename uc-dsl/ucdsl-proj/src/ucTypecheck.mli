(* UcTypecheck module interface *)

(* Typecheck a specification *)

open EcSymbols
open EcLocation
open EcEnv

open UcSpec
open UcTypedSpec

(* maximum number of message parameters allowed *)

val max_msg_params : int

(* typecheck a specification

   the first argument is the qualified name of the .uc file from which
   spec was lexed

   the second argument is used for typechecking uc_requires; the
   located symbol is the (capitalized) root name of the .uc file,
   normally located in the file it was lexed from *)

val typecheck :
  symbol -> (symbol located -> maps_tyd) -> spec -> maps_tyd

(* typecheck a real functionality expression *)

val inter_check_real_fun_expr :
  symbol -> maps_tyd -> fun_expr -> fun_expr_tyd

(*
(* typecheck a sent message expression in an environment *)

val inter_check_sent_msg_expr :
  maps_tyd -> env -> sent_msg_expr -> sent_msg_expr_tyd
*)
