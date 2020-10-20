(* A modification of src/ecCommands.mli of the EasyCrypt distribution

   See "UC DSL" for changes *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation

(* -------------------------------------------------------------------- *)
exception Restart

(* -------------------------------------------------------------------- *)
val addidir  : ?namespace:EcLoader.namespace -> ?recursive:bool -> string -> unit
val loadpath : unit -> (EcLoader.namespace option * string) list

(* -------------------------------------------------------------------- *)
type notifier = EcGState.loglevel -> string Lazy.t -> unit

type checkmode = {
  cm_checkall : bool;
  cm_timeout  : int;
  cm_cpufactor: int;
  cm_nprovers : int;
  cm_provers  : string list option;
  cm_profile  : bool;
  cm_iterate  : bool;
}

val initialize  :
     restart:bool
  -> undo:bool
  -> boot:bool
  -> checkmode:checkmode
  -> unit

val current     : unit -> UcEcScope.scope
val addnotifier : notifier -> unit

(* -------------------------------------------------------------------- *)
val process : ?timed:bool -> EcParsetree.global_action located -> float option

val undo  : int  -> unit
val reset : unit -> unit
val uuid  : unit -> int
val mode  : unit -> string

val check_eco : string -> bool

(* -------------------------------------------------------------------- *)
val pp_current_goal : ?all:bool -> Format.formatter -> unit
val pp_maybe_current_goal : Format.formatter -> unit

(* -------------------------------------------------------------------- *)
val pragma_verbose : bool -> unit
val pragma_g_prall : bool -> unit
val pragma_check   : UcEcScope.Ax.mode -> unit

exception InvalidPragma of string

val apply_pragma : string -> unit

(* UC DSL interface *)

(* initialization *)
val ucdsl_init : unit -> unit

(* add a notifier *)
val ucdsl_addnotifier : notifier -> unit

(* current scope *)
val ucdsl_current : unit -> UcEcScope.scope

(* update current scope *)
val ucdsl_update : UcEcScope.scope -> unit

(* require a theory *)
val ucdsl_require :
  string EcLocation.located option *
  (string EcLocation.located * string EcLocation.located option) *
  [ `Export | `Import ] option ->
  unit

(* begin scope with only prelude required, saving old scope *)
val ucdsl_new : unit -> unit

(* end scope, reverting to saved one, which is updated to
   include required theories of ended scope *)
val ucdsl_end : unit -> unit
