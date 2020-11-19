(* UcEcInterface module *)

(* Interface with EasyCrypt *)

open Batteries
open Format
open EcUtils
(*
open EcDecl
open EcTypes
open EcPath
*)
open UcMessage
(*
open UcTypes
*)
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

let exists_type (ty : string) : bool =
  Option.is_some (EcEnv.Ty.lookup_opt ([] , ty) (env ()))

let exists_operator (op : string) : bool = 
  Option.is_some (EcEnv.Op.lookup_opt ([], op) (env ()))

(* We flatten the Tfun tree to (return typ, list of arg typ).  For
   nullary ops the list is empty.  We use only op_ty from the operator
   declaration - type parameters are not used, and we're not interested
   in op body, just signature. *)
(*
let get_operator_sig (op : string) : typ * typ list =
  let ecsig = (snd (EcEnv.Op.lookup ([], op) (env ()))).op_ty.ty_node in

  let get_last_sym (path : EcPath.path) =
    match path.p_node with
    | EcPath.Psymbol sym     -> sym
    | EcPath.Pqname (_, sym) -> sym in

(*      let tconstrExpected (ty:EcTypes.ty) =
                match ty.ty_node with
                | EcTypes.Tconstr (t,l) -> (t,l)
                | _ -> raise (Failure "EcTypes.Tconstr expected in a sequence of Tconstrs")
        in*)

  let rec get_typ (tn : EcTypes.ty_node) : typ =
    match tn with
    | EcTypes.Tconstr (p, [])      -> Tconstr (get_last_sym p, None)
    | EcTypes.Tconstr (p, hd :: _) ->
        Tconstr (get_last_sym p, Some (get_typ hd.ty_node))
    | EcTypes.Tvar i               -> Tvar (EcIdent.name i)
    | _                            ->
        raise (Failure "EcTypes.Tconstr or EcTypes.Tvar expected.") in

  let rec get_typs (tt : EcTypes.ty * EcTypes.ty) (argTyps: typ list) :
      typ list =
    let fstTyp = get_typ (fst tt).ty_node in
    match (snd tt).ty_node with
    | EcTypes.Tconstr _     -> (get_typ (snd tt).ty_node) :: fstTyp :: argTyps
    | EcTypes.Tfun (t1, t2) -> get_typs (t1, t2) (fstTyp :: argTyps)
    | _                     -> raise (Failure "unexpected EcType") in

  match ecsig with
  | EcTypes.Tconstr _     -> (get_typ ecsig, [])
  | EcTypes.Tfun (t1, t2) ->
      let typs = get_typs (t1, t2) [] in
      (List.hd typs, List.rev (List.tl typs))
  | _                     -> raise (Failure "unexpected EcType")
  *)
