(* UcStackedScopes module interface *)

(* Maintains a mutable stack of scopes from EcScope, implementing
   operations to manipulate this stack using operations from
   EcScope *)

open EcLocation
open EcParsetree
open EcCommands

exception ScopesStackError  (* raised to signal an error *)

(* initialize stack of scopes to be the initial scope; the stack will
    subsequently always be non-empty *)

val scopes_stack_init : unit -> unit

(* get current scope -- top of stack *)

val current_scope : unit -> EcScope.scope
    
(* update current scope *)

val update_current_scope : EcScope.scope -> unit

(* push scope onto stack *)

val push_scope : EcScope.scope -> unit

(* add a notifier to current scope *)

val add_notifier : notifier -> unit

(* process a type declaration, operator declaration, axiom
   specification or theory cloning in the current scope, updating
   the scope *)

val process_type_decl    : ptydecl located        -> unit
val process_op_decl      : poperator located      -> unit
val process_axiom        : paxiom located         -> unit
val process_theory_clone : theory_cloning located -> unit

(* require a theory in the current scope, updating the current scope *)

type require_t =
    (* optional namespace *)
    psymbol option
    (* theory to require & optional alternative name for result of requiring *)
  * (psymbol * psymbol option)
    (* do we export or import the theory's definitions? *)
  * [ `Export | `Import ] option

val require_theory : require_t -> unit

(* pushes a scope onto the stack opening a new top-level required
   theory with the supplied name and theory mode, starting with a
   scope identical to one at the top of the stack except that the
   environment and required theories are reset to the ones from the
   prelude

   the scopes stack must be nonempty, and there must not be a proof in
   progress *)  

val require_theory_start  : string -> EcTheory.thmode -> unit

(* end the current scope, requiring in the previous one the result of
   exiting the current scope, first checking that a top-level theory
   with the supplied name is being exited, and that this theory was
   not already loaded *)

val require_theory_finish : string -> unit

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
