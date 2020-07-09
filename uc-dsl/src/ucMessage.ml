(* UcMessage module *)

open Batteries

type message_type =
  | WarningMessage
  | ErrorMessage

let message_type_str mt =
  match mt with
  | WarningMessage -> "warning"
  | ErrorMessage   -> "error"

let message res mt filename loco msg =
  let mt_str = message_type_str mt in
  match loco with
  | None     ->
      (Printf.fprintf stderr "[%s: %s] %s\n" mt_str filename msg; res ())
  | Some loc ->
      let loc_str = EcLocation.tostring loc in
      (Printf.fprintf
       stderr 
       "[%s: %s%s] %s\n" mt_str filename loc_str msg; res ())

let error_message = message (fun () -> exit 1) ErrorMessage

let warning_message = message (fun () -> ()) WarningMessage
