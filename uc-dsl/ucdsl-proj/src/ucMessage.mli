(* UcMessage module interface *)

(* Issue Error and Warning Messages *)

open Format

(* raise the exception Failure with the supplied string *)

val failure : string -> 'a

(* error/warning messages are issued in raw (intended for consumption
   by Emacs major mode for UC DSL or Proof General) or non-raw
   (intended for consumption by humans) format, depending upon the
   current Global State of the UC DSL tool - see UcState module

   the raw format consists of a filename, beginning line number,
   beginning column number, ending line number, and ending column
   number, in sequence, separated by single spaces, where the numbers
   all begin with 1 *)

exception ErrorMessageExn

(* issue a located error message on the standard error output, and
   then raise ErrorMessageExn; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val error_message : EcLocation.t -> (formatter -> unit) -> 'a

(* issue a located error message on the standard error output, and
   then exit with status 1; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val error_message_exit : EcLocation.t -> (formatter -> unit) -> 'a

(* issue a located warning message on the standard error output; the
   second argument is used to do formatted outputs to
   Format.err_formatter to output the body of the message *)

val warning_message : EcLocation.t -> (formatter -> unit) -> unit

(* issue a non-located error message on the standard error output, and
   then raise ErrorMessageExn; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val non_loc_error_message : (formatter -> unit) -> 'a

(* issue a non-located error message on the standard error output, and
   then exit with status 1; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val non_loc_error_message_exit : (formatter -> unit) -> 'a

(* issue a non-located warning message on the standard error output;
   the second argument is used to do formatted outputs to
   Format.err_formatter to output the body of the message *)

val non_loc_warning_message : (formatter -> unit) -> unit
