(* -------------------------------------------------------------------- *)
open EcIdent
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = private {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pqname  of path * symbol

(* -------------------------------------------------------------------- *)
val psymbol  : symbol -> path
val pqname   : path -> symbol -> path
val pqoname  : path option -> symbol -> path
val pappend  : path -> path -> path
val poappend : path -> path option -> path

val p_equal       : path -> path -> bool
val p_compare     : path -> path -> int
val p_ntr_compare : path -> path -> int
val p_hash        : path -> int

(* -------------------------------------------------------------------- *)
val tostring    : path -> string
val toqsymbol   : path -> qsymbol
val fromqsymbol : qsymbol -> path
val basename    : path -> symbol
val extend      : path -> symbol list -> path
val prefix      : path -> path option
val remprefix   : prefix:path -> path:path -> symbol list option
val isprefix    : prefix:path -> path:path -> bool
val rootname    : path -> symbol
val tolist      : path -> symbol list
val p_size      : path -> int

(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path
module Hp : EcMaps.EHashtbl.S with type key = path

module Sp : sig
  include Set.S with module M = Map.MakeBase(Mp)

  val ntr_elements : t -> elt list
end

(* -------------------------------------------------------------------- *)
module Mop : Map.S with type key = path option

(* -------------------------------------------------------------------- *)
type mpath = private {
  m_top  : mpath_top;
  m_args : mpath list;
  m_tag  : int;
}

and mpath_top =
[ | `Local of ident
  | `Concrete of path * path option ]

(* -------------------------------------------------------------------- *)
val mpath     : mpath_top -> mpath list -> mpath
val mpath_abs : ident -> mpath list -> mpath
val mqname    : mpath -> symbol -> mpath
val mastrip   : mpath -> mpath

val mident    : ident -> mpath
val mpath_crt : path -> mpath list -> path option -> mpath

val m_equal       : mpath -> mpath -> bool
val mt_equal      : mpath_top -> mpath_top -> bool
val m_compare     : mpath -> mpath -> int
val m_ntr_compare : mpath -> mpath -> int
val m_hash        : mpath -> int
val m_apply       : mpath -> mpath list -> mpath
val m_fv          : int EcIdent.Mid.t -> mpath -> int EcIdent.Mid.t

val is_abstract : mpath -> bool
val is_concrete : mpath -> bool

val m_functor : mpath -> mpath

val mget_ident : mpath -> ident
val mget_ident_opt : mpath -> ident option

val pp_m : Format.formatter -> mpath -> unit

(* -------------------------------------------------------------------- *)
type xpath = private {
  x_top : mpath;
  x_sub : symbol;
  x_tag : int;
}

val xpath     : mpath -> symbol -> xpath
val xastrip   : xpath -> xpath

val x_equal       : xpath -> xpath -> bool
val x_compare     : xpath -> xpath -> int
val x_ntr_compare : xpath -> xpath -> int
val x_hash        : xpath -> int

(* These functions expect xpath representing program variables
 * with a normalized [x_top] field. *)
val x_equal_na   : xpath -> xpath -> bool
val x_compare_na : xpath -> xpath -> int

val x_fv : int EcIdent.Mid.t -> xpath -> int EcIdent.Mid.t

val xbasename   : xpath -> symbol

(* -------------------------------------------------------------------- *)
val m_tostring : mpath -> string
val x_tostring : xpath -> string

(* -------------------------------------------------------------------- *)
module Mm : Map.S with type key = mpath
module Hm : EcMaps.EHashtbl.S with type key = mpath

module Sm : sig
  include Set.S with module M = Map.MakeBase(Mm)

  val ntr_elements : t -> elt list
end

(* -------------------------------------------------------------------- *)
module Mx : Map.S with type key = xpath
module Hx : EcMaps.EHashtbl.S with type key = xpath

module Sx : sig
  include Set.S with module M = Map.MakeBase(Mx)

  val ntr_elements : t -> elt list
end

(* -------------------------------------------------------------------- *)
type smsubst = {
  sms_crt : path Mp.t;
  sms_id  : mpath Mid.t;
}

val sms_identity : smsubst
val sms_is_identity : smsubst -> bool

val sms_bind_abs : ident -> mpath -> smsubst -> smsubst

val p_subst : path Mp.t -> path -> path
val m_subst : smsubst -> mpath -> mpath
val x_subst : smsubst -> xpath -> xpath

val m_subst_abs : mpath Mid.t -> mpath -> mpath
val x_subst_abs : mpath Mid.t -> xpath -> xpath
