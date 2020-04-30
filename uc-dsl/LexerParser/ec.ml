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

module EP = EcParsetree

(* -------------------------------------------------------------------- *)

let ecTheoriesDir = Filename.dirname "/home/tp/.opam/system/lib/easycrypt/theories/"

let ucTheoriesDir = Filename.dirname "/home/tp/Dropbox/Documents/EasyCrypt/DefLang/code/ecTryOuts/."

let checkmode = {
              EcCommands.cm_checkall  = false; 
              EcCommands.cm_timeout   = 3; 
              EcCommands.cm_cpufactor = 1; 
              EcCommands.cm_nprovers  = 4;
              EcCommands.cm_provers   = None;
              EcCommands.cm_wrapper   = None;
              EcCommands.cm_profile   = false;
              EcCommands.cm_iterate   = false;
            }

let notifier (lvl : EcGState.loglevel) (lazy msg) =
		match lvl with
		| `Critical -> raise (Failure ("EasyCrypt critical error:"^msg))
		|_ -> print_string ("EasyCrypt notification:"^msg)

(* -------------------------------------------------------------------- *)
let requireImport (th:string) =
  
  EcCommands.addidir ~system:true ~recursive:true ecTheoriesDir;
  EcCommands.addidir Filename.current_dir_name;
  EcCommands.addidir ucTheoriesDir;
  EcCommands.initialize ~restart:false ~undo:false ~boot:false ~checkmode;
  EcCommands.addnotifier notifier;
  (* Register user messages printers *)
  begin let open EcUserMessages in register () end;
  (
  match EcLocation.unloc (EcIo.parse (EcIo.from_string "require import "^th^".")) with
	| EP.P_Prog (commands, locterm) ->
              List.iter
                     (fun p->EcCommands.process ~timed:p.EP.gl_timed p.EP.gl_action)
                commands
	| EP.P_Undo _ -> raise (Failure "usage of internal keyword undo is unacceptable, sorry")
  );

let existsType (typ:string):bool = false

let existsOperator (op:string):bool = false

let getOperatorSig (op:string): string * string list = ("",[])



