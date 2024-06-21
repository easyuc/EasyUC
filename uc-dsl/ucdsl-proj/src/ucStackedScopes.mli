(* UcStackedScopes module interface *)

(* Maintains a mutable stack of scopes from EcScope, implementing
   operations to manipulate this stack using operations from
   EcScope *)

open EcParsetree
open EcCommands

(* initialize stack of scopes to be the initial scope; the stack will
    subsequently always be non-empty *)

val scopes_stack_init : unit -> unit

(* add a notifier to current scope *)

val add_notifier : notifier -> unit
    
(* get current scope -- top of stack *)

val current_scope : unit -> EcScope.scope
    
(* update current scope *)

val update_current_scope : EcScope.scope -> unit

(* require a theory in the current scope, updating the current scope *)

type require_t =
    (* optional namespace *)
    psymbol option
    (* theory to require & optional alternative name for result of requiring *)
  * (psymbol * psymbol option)
    (* do we export or import the theory's definitions? *)
  * [ `Export | `Import ] option

val require_theory : require_t -> unit

(* push new scope onto stack, created from the current one, but
    reverting the environment and required theories to the ones
    of the prelude *)

val new_scope : unit -> unit

(* end current scope, reverting to previous one from stack, which is
   updated to include required theories of ended scope *)

val end_scope : unit -> unit

(* end scope, reverting to previous one from stack, but ignoring the
   scope being ended *)

val end_scope_ignore : unit -> unit
