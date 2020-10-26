(* UcTypecheck module interface *)

(* Typecheck a specification *)

open UcSpec
open UcTypedSpec

(* the first argument is the filename (qualified relative to the current
   directory) of the locations of the spec

   the second argument is used for typechecking uc_requires *)

val typecheck : string -> (id -> typed_spec) -> spec -> typed_spec
