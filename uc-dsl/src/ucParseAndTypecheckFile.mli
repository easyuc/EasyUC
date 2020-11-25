(* UcParseAndTypecheckFile module interface *)

(* Parse and then typecheck a DSL specification *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open UcParseFile
open UcTypedSpec

val parse_and_typecheck_file_or_id : file_or_id -> typed_spec
