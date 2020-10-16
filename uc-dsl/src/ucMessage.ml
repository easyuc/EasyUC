(* UcMessage module *)

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

let message res mt loc msgf =
  let mt_str = message_type_str mt in
  let raw = UcState.get_raw_messages () in
  if raw
  then let loc_str = loc_to_str_raw loc in
       (Printf.eprintf "%s: %s\n\n" mt_str loc_str;
        msgf Format.err_formatter;
        Format.pp_print_newline Format.err_formatter ();
        res ())
  else let loc_str = loc_to_str loc in
       (Printf.eprintf "[%s: %s]\n\n" mt_str loc_str;
        msgf Format.err_formatter;
        Format.pp_print_newline Format.err_formatter ();
        res ())

let error_message = message (fun () -> exit 1) ErrorMessage

let warning_message = message (fun () -> ()) WarningMessage

let non_loc_message res mt msgf =
  let mt_str = message_type_str mt in
  let raw = UcState.get_raw_messages () in
  if raw
  then (Printf.eprintf "%s: \n\n" mt_str;
        msgf Format.err_formatter;
        Format.pp_print_newline Format.err_formatter ();
        res ())
  else (Printf.eprintf "[%s:]\n\n" mt_str;
        msgf Format.err_formatter;
        Format.pp_print_newline Format.err_formatter ();
        res ())

let non_loc_error_message = non_loc_message (fun () -> exit 1) ErrorMessage

let non_loc_warning_message = non_loc_message (fun () -> ()) WarningMessage

(* called to indicate that reaching a given code branch should
   be impossible *)

let failure msg = raise (Failure msg)
