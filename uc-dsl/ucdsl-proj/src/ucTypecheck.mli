(* UcTypecheck module interface *)

(* Typecheck a specification *)

open EcSymbols
open EcLocation
open EcEnv
open EcTypes

open UcSpecTypedSpecCommon
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
  symbol -> (symbol located -> typed_spec) -> spec -> typed_spec

(* typecheck a real functionality expression *)

val inter_check_real_fun_expr :
  symbol -> typed_spec -> fun_expr -> fun_expr_tyd

(* typecheck an unlocated root-qualified message path *)

val inter_check_root_qualified_msg_path :
  typed_spec -> msg_path_u -> (msg_dir * ty list) option

(* types for port and addr *)

val port_ty : ty
val addr_ty : ty

(* typecheck a sent message expression in an environment *)

val inter_check_sent_msg_expr :
  typed_spec -> env -> sent_msg_expr -> sent_msg_expr_tyd
