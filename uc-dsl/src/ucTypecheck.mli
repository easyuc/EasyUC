(* ucTypecheck.mli *)

(* Typecheck a specification *)

open UcSpec
open UcTypedSpec

val typecheck : spec -> typed_spec
