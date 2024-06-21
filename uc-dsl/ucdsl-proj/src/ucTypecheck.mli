(* UcTypecheck module interface *)

(* Typecheck a specification *)

open EcSymbols
open EcLocation
open EcTypes
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
   normally located in the file it was lexed from

   scopes and thus the current environment are manipulated in
   the background using the extapi_ commands of ecScope *)

val typecheck :
  symbol -> (symbol located -> maps_tyd) -> spec -> maps_tyd

(* typecheck a real functionality expression *)

val inter_check_real_fun_expr :
  symbol -> maps_tyd -> fun_expr -> fun_expr_tyd

(* check type in environment, rejecting type variables *)

val inter_check_type : env -> pty -> ty

(* typecheck an expression against an optional type with no unification
   of type variables *)

val inter_check_expr : env -> pexpr -> ty option -> expr * ty

(* typecheck a sent message expression in an environment *)

val inter_check_sent_msg_expr :
  maps_tyd -> env -> sent_msg_expr -> sent_msg_expr_tyd
