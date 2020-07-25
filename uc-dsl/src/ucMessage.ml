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
  then Printf.sprintf "from line %d columns %d to %d"
       (fst l.loc_start) (snd l.loc_start + 1) (snd l.loc_end + 1)
  else Printf.sprintf "from line %d column %d to line %d column %d"
       (fst l.loc_start) (snd l.loc_start + 1)
       (fst l.loc_end) (snd l.loc_end + 1)

let loc_to_str_raw (l : EcLocation.t) =
  Printf.sprintf "%d %d %d %d"
  (fst l.loc_start) (snd l.loc_start + 1) (fst l.loc_end) (snd l.loc_end + 1)

let message res mt filename loco msg =
  let mt_str = message_type_str mt in
  let raw = UcState.get_raw_messages () in
  if raw then
    match loco with
    | None     ->
        (Printf.fprintf stderr "%s: %s\n\n%s\n" mt_str filename msg; res ())
    | Some loc ->
        let loc_str = loc_to_str_raw loc in
        (Printf.fprintf
         stderr 
         "%s: %s %s\n\n%s\n" mt_str filename loc_str msg; res ())
  else match loco with
       | None     ->
           (Printf.fprintf stderr "[%s: %s]\n%s\n" mt_str filename msg; res ())
       | Some loc ->
           let loc_str = loc_to_str loc in
           (Printf.fprintf
            stderr 
            "[%s: %s %s]\n\n%s\n" mt_str filename loc_str msg; res ())

let error_message = message (fun () -> exit 1) ErrorMessage

let warning_message = message (fun () -> ()) WarningMessage
