(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcDecl
open EcTypes
open EcPath
module EP = EcParsetree

open UcTypes
(* -------------------------------------------------------------------- *)

let ecTheoriesDir = Filename.dirname UcConfig.ec_theories_dir_str

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
		| `Critical -> raise (Failure ("EasyCrypt critical error:"^msg))
		|_ -> print_string ("EasyCrypt notification:"^msg)

let initialized = ref false

let init () =
 if !initialized=false then
  (initialized:=true;
  EcCommands.addidir ~namespace:`System ~recursive:true ecTheoriesDir;
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

(* -------------------------------------------------------------------- *)

let executeCommand (c:string) =
  match EcLocation.unloc (EcIo.parse (EcIo.from_string c)) with
	| EP.P_Prog (commands, locterm) ->
              List.iter
               (fun p -> ignore (EcCommands.process ~timed:p.EP.gl_timed p.EP.gl_action))
               commands
	| EP.P_Undo _ -> raise (Failure "usage of internal keyword undo is unacceptable, sorry")

let requireImport (th:string) =
  executeCommand ("require import "^th^".")

let env () = EcScope.env (EcCommands.current())

let existsType (ty:string):bool =
	match EcEnv.Ty.lookup_opt ([],ty) (env()) with
	| Some x -> true
	| None -> false

let existsOperator (op:string):bool = 
	match EcEnv.Op.lookup_opt ([],op) (env()) with
	| Some x -> true
	| None -> false



(*
  We flatten the Tfun tree to (return typ, list of arg typ).
  For nullary ops the list is empty.
  We use only op_ty from the operator declaration - type parameters are not used,
  and we're not intrested in op body, just signature.
*)
let getOperatorSig (op:string): typ * typ list =
	let ecsig = (snd (EcEnv.Op.lookup ([],op) (env()) )).op_ty.ty_node 
	in
	let getLastSym (path:EcPath.path) =
		match path.p_node with
		| EcPath.Psymbol sym -> sym
		| EcPath.Pqname (pth,sym) -> sym
	in
(*	let tconstrExpected (ty:EcTypes.ty) =
		match ty.ty_node with
		| EcTypes.Tconstr (t,l) -> (t,l)
		| _ -> raise (Failure "EcTypes.Tconstr expected in a sequence of Tconstrs")
	in*)
	let rec getTyp (tn:EcTypes.ty_node) : typ=
		match tn with
		| EcTypes.Tconstr (p,[]) -> Tconstr ((getLastSym p),None)
		| EcTypes.Tconstr (p,hd::tl) -> Tconstr ((getLastSym p), Some (getTyp hd.ty_node))
		| EcTypes.Tvar i -> Tvar (EcIdent.name i)
		| _ -> raise (Failure "EcTypes.Tconstr or EcTypes.Tvar expected.")
	in
	let rec getTyps (tt:EcTypes.ty * EcTypes.ty) (argTyps: typ list) : typ list =
		let fstTyp = getTyp (fst tt).ty_node
		in
		match (snd tt).ty_node with
		| EcTypes.Tconstr (t,l) -> (getTyp (snd tt).ty_node)::fstTyp::argTyps
		| EcTypes.Tfun (t1,t2) -> getTyps (t1,t2) (fstTyp::argTyps)
		| _ -> raise (Failure "unexpected EcType")
	in
	match ecsig with
	| EcTypes.Tconstr (t,l) -> getTyp ecsig,[]
	| EcTypes.Tfun (t1,t2) -> let typs = getTyps (t1,t2) [] in (List.hd typs,List.rev (List.tl typs))
	| _ -> raise (Failure "unexpected EcType")



