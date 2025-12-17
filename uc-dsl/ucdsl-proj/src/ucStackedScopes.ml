(* UcStackedScopes module *)

open EcUtils
open EcLocation
open EcParsetree

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
  scopes_stack := [EcCommands.initial ~checkmode ~boot:false]

let current_scope () : EcScope.scope =
  oget ~exn:ScopesStackError (List.Exceptionless.hd !scopes_stack)
    
let update_current_scope (scope : EcScope.scope) : unit =
  scopes_stack := map_scopes (fun _ -> scope) (! scopes_stack)

let push_scope (scope : EcScope.scope) : unit =
  scopes_stack := scope :: !scopes_stack

let add_notifier (notifier : EcCommands.notifier) : unit =
  let gstate = EcScope.gstate (current_scope ()) in
  ignore (EcGState.add_notifier notifier gstate)

let process_op_decl (pop : poperator) : unit =
  let query = Goperator pop in
  let query = mk_loc _dummy query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let process_type_decl (ptyd : ptydecl) : unit =
  let query = Gtype [ptyd] in
  let query = mk_loc _dummy query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let process_axiom (pa : paxiom) : unit =
  let query = Gaxiom pa in
  let query = mk_loc _dummy query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let process_theory_clone (tc : theory_cloning) : unit =
  let query = GthClone tc in
  let query = mk_loc _dummy query in
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
  let new_ =
    EcScope.Theory.require_start ("_" ^ name, thmode) (current_scope ()) in
  scopes_stack := new_ :: (! scopes_stack)

let require_theory_finish (name : string) : unit =
  match !scopes_stack with
  | top :: rest ->
      (try
         let repl = EcScope.Theory.require_finish ("_" ^ name) top in
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
