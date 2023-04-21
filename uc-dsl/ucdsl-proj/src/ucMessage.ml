(* UcMessage module *)

let failure msg = raise (Failure msg)

type message_type =
  | WarningMessage
  | ErrorMessage

let message_type_str mt =
  match mt with
  | WarningMessage -> "warning"
  | ErrorMessage   -> "error"

(* make column numbers as well as line numbers begin from 1 *)

let loc_to_str (l : EcLocation.t) : string =
  if fst l.loc_start = fst l.loc_end
  then Printf.sprintf "%s: from line %d columns %d to %d"
       l.loc_fname (fst l.loc_start)
       (snd l.loc_start + 1) (snd l.loc_end + 1)
  else Printf.sprintf "%s: from line %d column %d to line %d column %d"
       l.loc_fname
       (fst l.loc_start) (snd l.loc_start + 1)
       (fst l.loc_end) (snd l.loc_end + 1)

let loc_to_str_raw (l : EcLocation.t) : string =
  Printf.sprintf "%s %d %d %d %d"
  l.loc_fname
  (fst l.loc_start) (snd l.loc_start + 1)
  (fst l.loc_end) (snd l.loc_end + 1)

let message res mt loc_opt msgf =
  let mt_str = message_type_str mt in
  let raw    = UcState.get_raw_messages () in
  (match loc_opt with
   | None     ->
       if raw
       then Printf.eprintf "%s:\n\n"   mt_str
       else Printf.eprintf "[%s:]\n\n" mt_str
   | Some loc ->
       if raw
       then Printf.eprintf "%s: %s\n\n"   mt_str (loc_to_str_raw loc)
       else Printf.eprintf "[%s: %s]\n\n" mt_str (loc_to_str loc));
  msgf Format.err_formatter;
  Format.pp_print_newline Format.err_formatter ();
  res ()

let error_message loc = message (fun () -> exit 1) ErrorMessage (Some loc)

let warning_message loc = message (fun () -> ()) WarningMessage (Some loc)

let non_loc_error_message = message (fun () -> exit 1) ErrorMessage None

let non_loc_warning_message = message (fun () -> ()) WarningMessage None

type loc_data = string * int * int * int * int

let loc_to_loc_data (l : EcLocation.t) =
  (l.loc_fname, fst l.loc_start, snd l.loc_start + 1,
   fst l.loc_end, snd l.loc_end + 1)

type message = message_type * loc_data option * string

exception ErrorMessageExn

let messages_ref : message list ref = ref []

let get_messages () =
  let xs = ! messages_ref in
  messages_ref := []; xs

let message_record res mt loc_opt msgf =
  let raw_opt = Option.map loc_to_loc_data loc_opt in
  let () = msgf Format.str_formatter in
  let s = Format.flush_str_formatter () in
  messages_ref := ! messages_ref @ [(mt, raw_opt, s)];
  res ()

let error_message_record loc =
  message_record (fun () -> raise ErrorMessageExn) ErrorMessage (Some loc)

let warning_message_record loc =
  message_record (fun () -> ()) WarningMessage (Some loc)

let non_loc_error_message_record =
  message_record (fun () -> raise ErrorMessageExn) ErrorMessage None

let non_loc_warning_message_record =
  message_record (fun () -> ()) WarningMessage None
