(* UcMessage module *)

open Batteries

type message_type =
  | WarningMessage
  | ErrorMessage

let message_type_str mt =
  match mt with
  | WarningMessage -> "warning"
  | ErrorMessage   -> "error"

(* make column numbers as well as line numbers begin from 1 *)

let loc_to_str (l : EcLocation.t) =
  if fst l.loc_start = fst l.loc_end
  then Printf.sprintf "%s: from line %d columns %d to %d"
       l.loc_fname (fst l.loc_start)
       (snd l.loc_start + 1) (snd l.loc_end + 1)
  else Printf.sprintf "%s: from line %d column %d to line %d column %d"
       l.loc_fname
       (fst l.loc_start) (snd l.loc_start + 1)
       (fst l.loc_end) (snd l.loc_end + 1)

let loc_to_str_raw (l : EcLocation.t) =
  Printf.sprintf "%s %d %d %d %d"
  l.loc_fname
  (fst l.loc_start) (snd l.loc_start + 1)
  (fst l.loc_end) (snd l.loc_end + 1)

let message res mt loc msg =
  let mt_str = message_type_str mt in
  let raw = UcState.get_raw_messages () in
  if raw
  then let loc_str = loc_to_str_raw loc in
       (Printf.eprintf
        "%s: %s\n\n%s\n" mt_str loc_str msg; res ())
  else let loc_str = loc_to_str loc in
       (Printf.eprintf
        "[%s: %s]\n\n%s\n" mt_str loc_str msg; res ())

let error_message = message (fun () -> exit 1) ErrorMessage

let warning_message = message (fun () -> ()) WarningMessage

let non_loc_error_message msg =
  let raw = UcState.get_raw_messages () in
  if raw
  then (Printf.eprintf
        "error: \n\n%s\n" msg; exit 1)
  else (Printf.eprintf
        "[error:]\n\n%s\n" msg; exit 1)

(* called to indicate that reaching a given code branch should
   be impossible *)

let failure msg =
  raise (Failure msg)
