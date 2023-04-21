(* UcMessage module interface *)

(* Issue Error and Warning Messages *)

open Format

(* raise the exception Failure with the supplied string *)

val failure : string -> 'a

(* error/warning messages are issued in raw (intended for consumption
   by Emacs major mode for UC DSL) or non-raw (intended for consumption
   by humans) format, depending upon the current Global State of
   the UC DSL tool - see UcState module

   the raw format consists of a filename, beginning line number,
   beginning column number, ending line number, and ending column
   number, in sequence, separated by single spaces, where the numbers
   all begin with 1 *)

(* issue a located error message on the standard error output, and
   then exit with status 1; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val error_message : EcLocation.t -> (formatter -> unit) -> 'a

(* issue a located warning message on the standard error output, which
   does *not* exit the process; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val warning_message : EcLocation.t -> (formatter -> unit) -> unit

(* issue a non-located error message on the standard error output, and
   then exit with status 1; the second argument is used to do
   formatted outputs to Format.err_formatter to output the body of the
   message *)

val non_loc_error_message : (formatter -> unit) -> 'a

(* issue a non-located warning message on the standard error output,
   which does *not* exit the process; the second argument is used to
   do formatted outputs to Format.err_formatter to output the body of
   the message *)

val non_loc_warning_message : (formatter -> unit) -> unit

(* the following types and functions are for when we want to
   collect messages, rather than issue them to the standard error
   output

   some of the functions manipulate a mutable queue of messages *)

type message_type =
  | WarningMessage
  | ErrorMessage

(* file location of error/warning

   line and column numbers are beginning with 1 *)

type loc_data =
  string *  (* filename *)
  int    *  (* start line *)
  int    *  (* start column *)
  int    *  (* end line *)
  int       (* end column *)

(* a message can optionally be localized *)

type message = message_type * loc_data option * string

exception ErrorMessageExn

(* get the issued messages, emptying the message queue *)

val get_messages : unit -> message list

(* issue a located error message, and then raise the exception
   ErrorMsgExn; the second argument is used to do formatted outputs to
   the string formatter, from which a string s is obtained; then the
   message (ErrorMessage, Some loc_data, s) is queued, where loc_data
   is the loc_data corresponding to the first argument *)

val error_message_record : EcLocation.t -> (formatter -> unit) -> 'a

(* issue a located warning message, and then return (); the second
   argument is used to do formatted outputs to the string formatter,
   from which a string s is obtained; then the message
   (WarningMessage, Some loc_data, s) is queued, where loc_data is the
   loc_data corresponding to the first argument *)

val warning_message_record : EcLocation.t -> (formatter -> unit) -> unit

(* issue a non-located error message, and then raise the exception
   ErrorMsgExn; the second argument is used to do formatted outputs to
   the string formatter, from which a string s is obtained; then the
   message (ErrorMessage, None, s) is queued *)

val non_loc_error_message_record : (formatter -> unit) -> 'a

(* issue a non-located warning message, and then return (); the second
   argument is used to do formatted outputs to the string formatter,
   from which a string s is obtained; then the message
   (WarningMessage, None, s) is queued *)

val non_loc_warning_message_record : (formatter -> unit) -> unit
