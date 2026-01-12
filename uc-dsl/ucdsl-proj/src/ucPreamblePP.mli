(* UcPreamblePP module interface *)

(* Pretty printing of UC spec preambles *)

open Format

open EcParsetree

type ppna = formatter -> unit  (* pp with no argument *)

(* ppna_list_sep sep ppnas returns a ppna that when given a formatter
   will print the elements of ppnas in sequence, separated by printing
   of sep *)

val ppna_list_sep : ('a, 'b, 'c, 'd, 'd, 'a) format6 -> ppna list -> ppna

(* the UC DSL parser and type checker only produces a proper subset of
   the types ptydecl, poperator, paxiom and theory_cloning of
   EcParsetree, and the following functions must not be called with
   other values

   the environment arguments should be the ones of the scopes in which
   the functions of UcEcInterface are called to process type declarations,
   operator declarations, axiom specifications and theory clonings *)

(* produce a ppna for printing an abstract type declaration *)

val pp_abstract_type_decl : ptydecl -> ppna

(* produce a ppna for printing an abstract operator declaration *)

val pp_abstract_op_decl : EcEnv.env -> poperator -> ppna

(* produce a ppna for printing an axiom *)

val pp_axiom : EcEnv.env -> paxiom -> ppna

(* produce a ppna for printing the cloning of a theory *)

val pp_theory_cloning : EcEnv.env -> theory_cloning -> ppna




