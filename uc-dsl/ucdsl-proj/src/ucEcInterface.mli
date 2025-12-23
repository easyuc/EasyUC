(* UcEcInterface module interface *)

(* Interface with EasyCrypt *)

(* initialize EasyCrypt *)

open EcLocation

val init : unit -> unit

(* return the environment of the current scope *)

val env : unit -> EcEnv.env

(* process a type declaration, operator declaration, axiom
   specification or theory cloning in the current scope, updating
   the scope *)

val process_type_decl    : EcParsetree.ptydecl located        -> unit
val process_op_decl      : EcParsetree.poperator located      -> unit
val process_axiom        : EcParsetree.paxiom located         -> unit
val process_theory_clone : EcParsetree.theory_cloning located -> unit

(* require an EasyCrypt theory *)

val require :
  string EcLocation.located    ->  (* theory *)
  [ `Export | `Import ] option ->  (* should we export/import the theory's
                                      definitions *)
  unit
