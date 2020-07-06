(* ucEcInterface.ml *)

(* Interface with EasyCrypt tool *)

open EcUtils
open EcDecl
open EcTypes
open EcPath
module EP = EcParsetree

open UcTypes
open UcConfig

let checkmode = {
    EcCommands.cm_checkall  = false; 
    EcCommands.cm_timeout   = 3; 
    EcCommands.cm_cpufactor = 1; 
    EcCommands.cm_nprovers  = 4;
    EcCommands.cm_provers   = None;
    EcCommands.cm_profile   = false;
    EcCommands.cm_iterate   = false;
  }

let notifier (lvl : EcGState.loglevel) (lazy msg) =
  match lvl with
  | `Critical -> raise (Failure ("EasyCrypt critical error:" ^ msg))
  | _         -> print_string ("EasyCrypt notification:" ^ msg)

let initialized = ref false

let init () =
 if not (!initialized) then
   (initialized := true;
    EcCommands.addidir ~namespace:`System ~recursive:true ec_theories_dir;
    EcCommands.addidir ~namespace:`System ~recursive:false
    Filename.current_dir_name;
    (let include_dirs = UcState.get_include_dirs() in
     List.iter
     (fun x ->
      EcCommands.addidir ~namespace:`System ~recursive:false x)
     include_dirs);
    EcCommands.initialize ~restart:false ~undo:false ~boot:false ~checkmode;
    EcCommands.addnotifier notifier;
    (* Register user messages printers *)
    begin let open EcUserMessages in register () end)
  else ()

let execute_command (c : string) =
  match EcLocation.unloc (EcIo.parse (EcIo.from_string c)) with
  | EP.P_Prog (commands, _) ->
      List.iter
      (fun p -> ignore (EcCommands.process ~timed:p.EP.gl_timed p.EP.gl_action))
      commands
  | EP.P_Undo _ ->
      raise (Failure "usage of internal keyword undo is unacceptable, sorry")

let require_import (th : string) =
  execute_command ("require import " ^ th ^ ".")

let env () = EcScope.env (EcCommands.current())

let exists_type (ty : string) : bool =
  Option.is_some (EcEnv.Ty.lookup_opt ([] , ty) (env ()))

let exists_operator (op : string) : bool = 
  Option.is_some (EcEnv.Op.lookup_opt ([], op) (env ()))

(* We flatten the Tfun tree to (return typ, list of arg typ).  For
   nullary ops the list is empty.  We use only op_ty from the operator
   declaration - type parameters are not used, and we're not intrested
   in op body, just signature. *)

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
