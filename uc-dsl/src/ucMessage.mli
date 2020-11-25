(* UcMessage module interface *)

(* Issue Error and Warning Messages *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open Format

val error_message : EcLocation.t -> (formatter -> unit) -> 'a

val warning_message : EcLocation.t -> (formatter -> unit) -> unit

val non_loc_error_message : (formatter -> unit) -> 'a

val non_loc_warning_message : (formatter -> unit) -> unit

val failure : string -> 'a
