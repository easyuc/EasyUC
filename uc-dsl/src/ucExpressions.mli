(* ucExpressions.mli *)

open UcTypes
open UcSpec

val check_expression : (qid -> typ) -> expressionL -> typ
val is_distribution : typ -> bool
val get_distribution_typ : typ -> typ
