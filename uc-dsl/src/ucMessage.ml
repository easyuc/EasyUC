(* UcMessage module *)

open Batteries

type message_type =
  | WarningMessage
  | ErrorMessage

let message_type_str mt =
  match mt with
  | WarningMessage -> "warning"
  | ErrorMessage   -> "error"

let loc_to_str_raw (p : EcLocation.t) =
  Printf.sprintf "%d %d %d %d"
  (fst p.loc_start) (snd p.loc_start) (fst p.loc_end) (snd p.loc_end)

let message res mt filename loco msg =
  let mt_str = message_type_str mt in
  let raw = UcState.get_raw_messages() in
  if raw then
    match loco with
    | None     ->
        (Printf.fprintf stderr "%s %s\n%s\n" mt_str filename msg; res ())
    | Some loc ->
        let loc_str = loc_to_str_raw loc in
        (Printf.fprintf
         stderr 
         "%s %s %s\n%s\n" mt_str filename loc_str msg; res ())
  else match loco with
       | None     ->
           (Printf.fprintf stderr "[%s: %s] %s\n" mt_str filename msg; res ())
       | Some loc ->
           let loc_str = EcLocation.tostring loc in
           (Printf.fprintf
            stderr 
            "[%s: %s%s] %s\n" mt_str filename loc_str msg; res ())

let error_message = message (fun () -> exit 1) ErrorMessage

let warning_message = message (fun () -> ()) WarningMessage
