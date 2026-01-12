(* UcStackedScopes module *)

open EcUtils
open EcLocation
open EcParsetree

type scopes_stack = (EcScope.scope list) ref

let scopes_stack : scopes_stack = ref []

exception InvalidScopesStack

let map_scopes (f : EcScope.scope -> EcScope.scope)
    (stacks : EcScope.scope list) =
  match stacks with
  | []              -> raise InvalidScopesStack
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
  oget ~exn:InvalidScopesStack (List.Exceptionless.hd !scopes_stack)
    
let update_current_scope (scope : EcScope.scope) : unit =
  scopes_stack := map_scopes (fun _ -> scope) (! scopes_stack)

let add_notifier (notifier : EcCommands.notifier) =
  let gstate = EcScope.gstate (current_scope ()) in
  ignore (EcGState.add_notifier notifier gstate)

type require_t =
    psymbol option
  * (psymbol * psymbol option)
  * [ `Export | `Import ] option

let require_theory ((nm, name, export) : require_t) =
  let query = GthRequire (nm, [name], export) in
  let query = mk_loc _dummy query in
  scopes_stack :=
  map_scopes
  (fun top -> EcCommands.process_internal EcCommands.loader top query)
  (! scopes_stack)

let new_scope () =
  let newscope = EcScope.for_loading (current_scope ()) in
  scopes_stack := newscope :: !scopes_stack

let end_scope () =
  match !scopes_stack with
  | top :: prev :: rest ->
      let new_scope =
        EcScope.Theory.update_with_required ~dst:prev ~src:top in
      scopes_stack := new_scope :: rest
  | _                   -> raise InvalidScopesStack

let end_scope_ignore () =
  match !scopes_stack with
  | _ :: ((_ :: _) as rest) -> scopes_stack := rest
  | _                       -> raise InvalidScopesStack
