(* UcMessage module interface *)

(* Issue Error and Warning Messages *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open Format

(* error/warning messages are issued in raw (intended for consumption
   by Emacs major mode for UC DSL) or non-raw (intended for consumption
   by humans) format, depending upon the current Global State of
   the UC DSL tool - see UcState module *)

(* issue a located error message on the standard error output, and
   then exit with status 1; the second argument does formatted outputs
   to Format.err_formatter to output the body of the message *)

val error_message : EcLocation.t -> (formatter -> unit) -> 'a

(* issue a located warning message on the standard error output, which
   does *not* exit the process; the second argument does formatted
   outputs to Format.err_formatter to output the body of the message
   *)

val warning_message : EcLocation.t -> (formatter -> unit) -> unit

(* issue a non-located error message on the standard error output, and
   then exit with status 1; the second argument does formatted outputs
   to Format.err_formatter to output the body of the message *)

val non_loc_error_message : (formatter -> unit) -> 'a

(* issue a non-located warning message on the standard error output,
   which does *not* exit the process; the second argument does
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val non_loc_warning_message : (formatter -> unit) -> unit

(* raise the exception Failure with the supplied string *)

val failure : string -> 'a
