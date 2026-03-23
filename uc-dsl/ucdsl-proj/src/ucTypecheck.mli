(* UcTypecheck module interface *)

(* Typecheck a specification *)

open EcSymbols
open EcLocation
open EcParsetree
open EcTypes
open EcFol
open EcEnv

open UcSpec
open UcTypedSpec

(* maximum number of message parameters allowed *)

val max_msg_params : int

type typecheck_mode =
  | TM_Top
  | TM_Theory

(* typecheck a specification

   the first argument is the qualified name of the .uc file from which
   spec was lexed; from this, the root is calculated

   if the second argument is TM_Top, the root will be prepended with
   "_", and so the maps will be updated with this modified symbol;
   this is used when typechecking does not happen inside a theory

   if the first argument is TM_Theory, the root will not be prepended
   with "_"; this is used when typechecking is happening inside the
   theory "UC_" ^ root

   the third argument is used for typechecking uc_requires; the
   located symbol is the (capitalized) root name of the .uc file,
   normally located in the file it was lexed from

   scopes and thus the current environment are manipulated in the
   background *)

val typecheck :
  symbol -> typecheck_mode -> (symbol located -> maps_tyd) ->
  spec -> maps_tyd

(* typecheck a real functionality expression *)

val inter_check_real_fun_expr :
  symbol -> maps_tyd -> fun_expr -> fun_expr_tyd

(* check type in environment, rejecting type variables *)

val inter_check_type : env -> pty -> ty

(* typecheck an expression against an optional type with no unification
   of type variables *)

val inter_check_expr : env -> pformula -> ty option -> form * ty

(* typecheck a sent message expression in an environment *)

val inter_check_sent_msg_expr :
  maps_tyd -> env -> sent_msg_expr -> sent_msg_expr_tyd
