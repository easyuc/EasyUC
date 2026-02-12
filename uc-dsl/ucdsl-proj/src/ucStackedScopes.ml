(* UcStackedScopes module *)

open EcUtils
open EcLocation
open EcParsetree
open EcScope

type scopes_stack = (EcScope.scope list) ref

let scopes_stack : scopes_stack = ref []

exception ScopesStackError

let map_scopes (f : EcScope.scope -> EcScope.scope)
    (stacks : EcScope.scope list) =
  match stacks with
  | []              -> raise ScopesStackError
  | stack :: stacks -> f stack :: stacks

let scopes_stack_init () : unit =
  let checkmode = EcCommands.{
      cm_checkall  = false;
      cm_timeout   = 0;
      cm_cpufactor = 1;
      cm_nprovers  = 0;
      cm_provers   = None;
      cm_profile   = false;
      cm_iterate   = false;
  } in
  scopes_stack := [EcCommands.initial ~checkmode ~boot:false ~checkproof:false]

let current_scope () : EcScope.scope =
  oget ~exn:ScopesStackError (List.Exceptionless.hd !scopes_stack)
    
let update_current_scope (scope : EcScope.scope) : unit =
  scopes_stack := map_scopes (fun _ -> scope) (! scopes_stack)

let push_scope (scope : EcScope.scope) : unit =
  scopes_stack := scope :: !scopes_stack

let add_notifier (notifier : EcCommands.notifier) : unit =
  let gstate = EcScope.gstate (current_scope ()) in
  ignore (EcGState.add_notifier notifier gstate)

let process_type_decl (ptyd : ptydecl located) : unit =
  let query = Gtype [unloc ptyd] in
  let query = mk_loc (loc ptyd) query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let process_op_decl (pop : poperator located) : unit =
  let query = Goperator (unloc pop) in
  let query = mk_loc (loc pop) query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let process_axiom (pa : paxiom located) : unit =
  let query = Gaxiom (unloc pa) in
  let query = mk_loc (loc pa) query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let process_theory_clone (tc : theory_cloning located) : unit =
  let query = GthClone (unloc tc) in
  let query = mk_loc (loc tc) query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

type require_t =
    psymbol option
  * (psymbol * psymbol option)
  * [ `Export | `Import ] option

let require_theory ((nm, name, export) : require_t) : unit =
  let query = GthRequire (nm, [name], export) in
  let query = mk_loc _dummy query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let require_theory_start (name : string) (thmode : EcTheory.thmode) : unit =
  let new_ = EcScope.Theory.require_start (current_scope ()) name thmode in
  scopes_stack := new_ :: (! scopes_stack)

let require_theory_finish (name : string) : unit =
  match !scopes_stack with
  | top :: rest ->
      (try
         let ri =
           {rqd_name      = name;
            rqd_namespace = None;   (* dummy *)
            rqd_kind      = `EcA;   (* dummy *)
            rqd_digest    = "";     (* dummy *)
            rqd_direct    = false;  (* dummy *)
           } in
         let repl = EcScope.Theory.require_finish ~new_:top ri in
         scopes_stack := repl :: rest
       with e -> raise e)
  | _           -> raise ScopesStackError

let new_scope () : unit =
  let new_ = EcScope.for_loading (current_scope ()) in
  scopes_stack := new_ :: !scopes_stack

let end_scope () : unit =
  match !scopes_stack with
  | top :: prev :: rest ->
      let new_scope =
        EcScope.Theory.update_with_required ~dst:prev ~src:top in
      scopes_stack := new_scope :: rest
  | _                   -> raise ScopesStackError

let end_scope_ignore () : unit =
  match !scopes_stack with
  | _ :: ((_ :: _) as rest) -> scopes_stack := rest
  | _                       -> raise ScopesStackError
