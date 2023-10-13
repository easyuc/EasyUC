(* UcMessage module *)

let failure msg = raise (Failure msg)

type message_type =
  | WarningMessage
  | ErrorMessage

let message_type_str mt =
  match mt with
  | WarningMessage -> "warning"
  | ErrorMessage   -> "error"

let loc_is_stdin (l : EcLocation.t) : bool = l.loc_fname = "stdin"

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

let loc_to_str_pg (l : EcLocation.t) : string =
  let startpos = UcState.get_pg_start_pos() in
  Printf.sprintf "%d-%d"
  (max 0 (l.loc_bchar - startpos))
  (max 0 (l.loc_echar - startpos))

exception ErrorMessageExn

let message res mt loc_opt msgf =
  let mt_str  = message_type_str mt in
  (* raw and pg_mode will never both be set *)
  let raw     = UcState.get_raw_messages () in
  let pg_mode = UcState.get_pg_mode () in
  (match loc_opt with
   | None     ->
       if raw
         then Printf.eprintf "%s:\n\n" mt_str
       else if pg_mode
         then Printf.eprintf "[%s:%s]\n\n" mt_str 
              (loc_to_str_pg EcLocation._dummy)
       else Printf.eprintf "[%s:]\n\n" mt_str
   | Some loc ->
       if raw
         then Printf.eprintf "%s: %s\n\n" mt_str (loc_to_str_raw loc)
       else if pg_mode
         then Printf.eprintf "[%s:%s]\n\n" mt_str (loc_to_str_pg loc)
       else if loc_is_stdin loc
         then Printf.eprintf "[%s:]\n\n" mt_str
       else Printf.eprintf "[%s: %s]\n\n" mt_str (loc_to_str loc)
  );
  msgf Format.err_formatter;
  Format.pp_print_newline Format.err_formatter ();
  if (pg_mode && (mt = WarningMessage)) then
    begin
      Printf.eprintf ";";
      Format.pp_print_newline Format.err_formatter ()
    end;
  res ()

let error_message loc =
  message (fun () -> raise ErrorMessageExn) ErrorMessage (Some loc)

let error_message_exit loc =
  message (fun () -> exit 1) ErrorMessage (Some loc)

let warning_message loc = message (fun () -> ()) WarningMessage (Some loc)

let non_loc_error_message =
  message (fun () -> raise ErrorMessageExn) ErrorMessage None

let non_loc_error_message_exit =
  message (fun () -> exit 1) ErrorMessage None

let non_loc_warning_message = message (fun () -> ()) WarningMessage None

let opt_loc_error_message =
  message (fun () -> raise ErrorMessageExn) ErrorMessage

let opt_loc_error_message_exit =
  message (fun () -> exit 1) ErrorMessage

let opt_loc_warning_message = message (fun () -> ()) WarningMessage

let debugging_message msgf =
  if UcState.get_debugging ()
  then begin
    if UcState.get_pg_mode ()
    then begin
      Printf.eprintf "\n<dbg>\n";
      msgf Format.err_formatter;
      Format.pp_print_newline Format.err_formatter ();
      Printf.eprintf "</dbg>\n"
    end
    else begin  
      Printf.eprintf "debugging:\n\n";
      msgf Format.err_formatter;
      Format.pp_print_newline Format.err_formatter ()
    end
  end
