(* -------------------------------------------------------------------- *)
open EcPath
open EcParsetree
open EcFol
open EcCoreGoal.FApi
open EcMatching.Position

(* -------------------------------------------------------------------- *)
val t_failure_event :
     codepos1
  -> form -> form -> form -> form
  -> (xpath * form) list
  -> form
  -> backward

(* -------------------------------------------------------------------- *)
val process_fel : pcodepos1 -> fel_info -> backward
