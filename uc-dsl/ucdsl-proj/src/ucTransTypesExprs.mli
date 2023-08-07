(* UcTransTypesExpr module interface *)

(* Translating (and checking) types and expressions from concrete to
   abstract syntax *)

(* Adapted from src/ecTyping.mli of the EasyCrypt distribution *)

open EcUtils
open EcSymbols
open EcEnv
open EcTypes
open UcSpec

type opmatch = [
  | `Op   of EcPath.path * EcTypes.ty list
  | `Lc   of EcIdent.t
  | `Var  of EcTypes.prog_var
  | `Proj of EcTypes.prog_var * EcMemory.proj_arg
]

type fxerror =
  | FXE_EmptyMatch
  | FXE_MatchParamsMixed
  | FXE_MatchParamsDup
  | FXE_MatchParamsUnk
  | FXE_MatchNonLinear
  | FXE_MatchDupBranches
  | FXE_MatchPartial
  | FXE_CtorUnk
  | FXE_CtorAmbiguous
  | FXE_CtorInvalidArity of (symbol * int * int)

type tyerror =
  | UniVarNotAllowed
  | TypeVarNotAllowed
  | UnboundTypeParameter   of symbol
  | UnknownTypeName        of qsymbol
  | UnknownTypeClass       of qsymbol
  | UnknownRecFieldName    of qsymbol
  | DuplicatedRecFieldName of symbol
  | MissingRecField        of symbol
  | MixingRecFields        of EcPath.path tuple2
  | UnknownProj            of qsymbol
  | AmbiguousProj          of qsymbol
  | AmbiguousProji         of int * ty
  | InvalidTypeAppl        of qsymbol * int * int
  | DuplicatedTyVar
  | DuplicatedField        of symbol
  | NonLinearPattern
  | TypeMismatch           of (ty * ty) * (ty * ty)
  | TypeClassMismatch
  | NotAFunction
  | NotAnInductive
  | UnknownVarOrOp         of qsymbol * ty list
  | MultipleOpMatch        of qsymbol * ty list *
                              (opmatch * EcUnify.unienv) list
  | InvalidMatch           of fxerror
  | PatternNotAllowed
  | UnknownScope           of qsymbol

exception TyError of EcLocation.t * env * tyerror

(* issue a type error for a type or expression *)

val tyerror : EcLocation.t -> env -> tyerror -> 'a

(* given an environment and unification environment, and a location
   for error messages, try to unify a type with an expected type
   (modifying the unification environment) *)

val unify_or_fail :
  env -> EcUnify.unienv -> EcLocation.t -> expct:ty -> ty -> unit

type typolicy  (* how should "_" and type variables be treated? *)

val tp_relax   : typolicy  (* allows both "_" and type variables *)
val tp_tydecl  : typolicy  (* allows only type variables *)
val tp_nothing : typolicy  (* allows neither "_" nor type variables *)

(* given an environment and type policy, translate a type from
   concrete to abstract syntax (modifying the unification environment)
   *)

val transty : typolicy -> env -> EcUnify.unienv -> pty -> ty

(* given an environment and type policy, translate a list of types
   from concrete to abstract syntax (modifying the unification
   environment) *)

val transtys : typolicy -> env -> EcUnify.unienv -> pty list -> ty list

(* given an environment and unification environment, translate instantiation
   of type variables (modifying the unification environment) *)

val transtvi : env -> EcUnify.unienv -> ptyinstan -> EcUnify.tvar_inst

(* given an environment and unification environment, translate an
   expression from concrete to abstract syntax, yielding an abstract
   type (modifying the unification environment) *)

val transexp : env -> EcUnify.unienv -> pexpr -> expr * ty

(* given an environment, unification environment and expected type,
   translate an expression from concrete to abstract syntax (modifying
   the unification environment) *)

val transexpcast : env -> EcUnify.unienv -> ty -> pexpr -> expr
