(* UcEcInterface module *)

(* Interface with EasyCrypt *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open Batteries
open Format
open EcUtils
open UcMessage
open UcConfig

(* EasyCrypt critical errors cause termination with an error message,
   but EasyCrypt warnings are collected in a list, which may be retrieved
   or reset *)

let ec_warnings = ref []

let get_ec_warnings () = ! ec_warnings

let reset_ec_warnings () = ec_warnings := []

let notifier (lvl : EcGState.loglevel) (lazy msg) =
  match lvl with
  | `Debug    -> ()  (* won't happen, given default log level *)
  | `Info     -> ()  (* discard *)
  | `Warning  -> ec_warnings := ! ec_warnings @ [msg]
  | `Critical ->
      non_loc_error_message
      (fun ppf -> fprintf ppf "@[EasyCrypt@ critical@ error:@;<1 2>%s@]" msg)

let initialized = ref false

let init () =
 if not (!initialized) then
   (initialized := true;

    (* include path setup *)
    (* lowest precedence *)
    EcCommands.addidir ~namespace:`System ~recursive:true ec_theories_dir;
    (* medium precedence; we have to reverse the include dirs
       list because we keep it in order from highest precedence to
       lowest *)
    (let include_dirs = List.rev (UcState.get_include_dirs()) in
     List.iter
     (fun x ->
      EcCommands.addidir ~namespace:`System ~recursive:false x)
     include_dirs);
    (* medium high precedence *)
    EcCommands.addidir ~namespace:`System ~recursive:false
    Filename.current_dir_name;
    (* highest precedence *)
    EcCommands.addidir ~namespace:`System ~recursive:false
    UcConfig.uc_prelude_dir;

    EcCommands.ucdsl_init ();    
    EcCommands.ucdsl_addnotifier notifier;

    reset_ec_warnings ();
    (* Register user messages printers *)
    begin let open EcUserMessages in register () end)
  else ()

let env () = EcScope.env (EcCommands.ucdsl_current ())

let require id io =
  try EcCommands.ucdsl_require (None, (id, None), io) with
  | EcScope.HiScopeError (_, msg)         ->
      error_message (EcLocation.loc id) 
      (fun ppf ->
         fprintf ppf
         ("@[EasyCrypt:@ error@ require@ importing@ " ^^
          "theory:@;<1 2>%s@]")
         msg)
  | EcScope.ImportError (None, name, e)   ->
      error_message (EcLocation.loc id)
      (fun ppf ->
         fprintf ppf
         "@[EasyCrypt:@ In@ external@ theory@ %s@;<1 2>%a@]"
         name EcPException.exn_printer e)
  | EcScope.ImportError (Some l, name, e) ->
      let l = {l with loc_fname = (EcLocation.unloc id) ^ ".ec"} in
      error_message (EcLocation.loc id)
      (fun ppf ->
         fprintf ppf
         "@[EasyCrypt:@ In@ external@ theory@ %s@ [%s]:@;<1 2>%a@]"
         name (EcLocation.tostring l) EcPException.exn_printer e)
  | _                                       ->
      error_message (EcLocation.loc id)
      (fun ppf ->
         fprintf ppf "@[EasyCrypt:@ error@ require@ importing@ theory@]")
