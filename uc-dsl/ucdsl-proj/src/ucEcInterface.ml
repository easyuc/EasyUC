(* UcEcInterface module *)

open Batteries
open Format
open EcUtils
open UcMessage
open UcConfig

let notifier (lvl : EcGState.loglevel) (lazy msg) =
  match lvl with
  | `Debug    -> ()  (* won't happen, given default log level *)
  | `Info     -> ()  (* discard *)
  | `Warning  ->
      non_loc_warning_message
      (fun ppf -> fprintf ppf "@[EasyCrypt@ warning:@;<1 2>%s@]" msg)
  | `Critical ->
      non_loc_error_message
      (fun ppf -> fprintf ppf "@[EasyCrypt@ critical@ error:@;<1 2>%s@]" msg)

let init_smt () =
    let cp_why3conf ~exists ~mode : string option=
      let confs =
        XDG.Config.file
          ~exists ~mode ~appname:EcVersion.app "why3.conf" in
      List.nth_opt confs 0
   in
   let why3conf = cp_why3conf ~exists:true ~mode:`All
   and ovrevict = [] in
   try
     EcProvers.initialize ~ovrevict ?why3conf ()
   with _ ->  
     non_loc_error_message_exit
     (fun ppf -> fprintf ppf "@[why3@ failed@ to@ initialize]")

let initialized = ref false

let init () =
 if not (!initialized) then
   (initialized := true;
    init_smt ();
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

    UcStackedScopes.scopes_stack_init ();    
    UcStackedScopes.add_notifier notifier;

    (* Register user messages printers *)
    begin let open EcUserMessages in register () end)
  else ()

let env () = EcScope.env (UcStackedScopes.current_scope ())

let require id io =
  try UcStackedScopes.require_theory (None, (id, None), io) with
  | EcScope.TopError (loc, exn) ->
      (match exn with
       | EcScope.HiScopeError (_, msg)         ->
           error_message (EcLocation.loc id) 
           (fun ppf ->
              fprintf ppf
              ("@[EasyCrypt:@ error@ requiring " ^^
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
       | _                                     ->
           error_message (EcLocation.loc id)
           (fun ppf ->
              fprintf ppf "@[EasyCrypt:@ error@ requiring theory@]"))
  | _                           ->
      error_message (EcLocation.loc id)
      (fun ppf ->
         fprintf ppf "@[EasyCrypt:@ error@ requiring theory@]")
