(* UcTypecheck module interface *)

(* Typecheck a specification *)

open EcSymbols
open EcLocation
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
  string -> (symbol located -> typed_spec) -> spec -> typed_spec
