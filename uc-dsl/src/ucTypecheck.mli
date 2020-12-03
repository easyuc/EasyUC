(* UcTypecheck module interface *)

(* Typecheck a specification *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcSymbols
open EcLocation
open UcSpec
open UcTypedSpec

(* typecheck a specification

   the first argument is the filename (qualified relative to the current
   directory) of the locations of the spec

   the second argument is used for typechecking uc_requires; the located
   symbol is the root name of the .uc file, normally located in the
   file it was lexed from *)

val typecheck : string -> (symbol located -> typed_spec) -> spec -> typed_spec
