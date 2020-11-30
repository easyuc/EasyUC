(* UcTypecheckTypesExpr module interface *)

(* Typechecking types and expressions *)

(* Adapted from src/ecTyping.mli of the EasyCrypt distribution, which
   has the following copyright: *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcUtils
open EcSymbols
open EcEnv
open EcPath
open EcTypes
open EcModules
open UcSpec

type opmatch = [
  | `Op   of EcPath.path * EcTypes.ty list
  | `Lc   of EcIdent.t
  | `Var  of EcTypes.prog_var
  | `Proj of EcTypes.prog_var * EcTypes.ty * (int * int)
]

type mismatch_funsig =
  | MF_targs of ty * ty (* expected, got *)
  | MF_tres  of ty * ty (* expected, got *)
  | MF_restr of EcEnv.env * [`Eq of Sx.t * Sx.t | `Sub of Sx.t ]

type tymod_cnv_failure =
  | E_TyModCnv_ParamCountMismatch
  | E_TyModCnv_ParamTypeMismatch of EcIdent.t
  | E_TyModCnv_MissingComp       of symbol
  | E_TyModCnv_MismatchFunSig    of symbol * mismatch_funsig
  | E_TyModCnv_SubTypeArg        of
      EcIdent.t * module_type * module_type * tymod_cnv_failure

type modapp_error =
  | MAE_WrongArgCount      of int * int  (* expected, got *)
  | MAE_InvalidArgType     of EcPath.mpath * tymod_cnv_failure
  | MAE_AccesSubModFunctor

type modtyp_error =
  | MTE_IncludeFunctor
  | MTE_InnerFunctor
  | MTE_DupProcName of symbol

type modsig_error =
  | MTS_DupProcName of symbol
  | MTS_DupArgName  of symbol * symbol

type funapp_error =
  | FAE_WrongArgCount

type mem_error =
  | MAE_IsConcrete

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

type filter_error =
  | FE_InvalidIndex of int
  | FE_NoMatch

type tyerror =
  | UniVarNotAllowed
  | FreeTypeVariables
  | TypeVarNotAllowed
  | OnlyMonoTypeAllowed    of symbol option
  | UnboundTypeParameter   of symbol
  | UnknownTypeName        of qsymbol
  | UnknownTypeClass       of qsymbol
  | UnknownRecFieldName    of qsymbol
  | UnknownInstrMetaVar    of symbol
  | UnknownMetaVar         of symbol
  | UnknownProgVar         of qsymbol * EcMemory.memory
  | DuplicatedRecFieldName of symbol
  | MissingRecField        of symbol
  | MixingRecFields        of EcPath.path tuple2
  | UnknownProj            of qsymbol
  | AmbiguousProj          of qsymbol
  | AmbiguousProji         of int * ty
  | InvalidTypeAppl        of qsymbol * int * int
  | DuplicatedTyVar
  | DuplicatedLocal        of symbol
  | DuplicatedField        of symbol
  | NonLinearPattern
  | LvNonLinear
  | NonUnitFunWithoutReturn
  | TypeMismatch           of (ty * ty) * (ty * ty)
  | TypeClassMismatch
  | TypeModMismatch        of mpath * module_type * tymod_cnv_failure
  | NotAFunction
  | NotAnInductive
  | AbbrevLowArgs
  | UnknownVarOrOp         of qsymbol * ty list
  | MultipleOpMatch        of qsymbol * ty list *
                              (opmatch * EcUnify.unienv) list
  | UnknownModName         of qsymbol
  | UnknownTyModName       of qsymbol
  | UnknownFunName         of qsymbol
  | UnknownModVar          of qsymbol
  | UnknownMemName         of symbol
  | InvalidFunAppl         of funapp_error
  | InvalidModAppl         of modapp_error
  | InvalidModType         of modtyp_error
  | InvalidModSig          of modsig_error
  | InvalidMem             of symbol * mem_error
  | InvalidMatch           of fxerror
  | InvalidFilter          of filter_error
  | FunNotInModParam       of qsymbol
  | NoActiveMemory
  | PatternNotAllowed
  | MemNotAllowed
  | UnknownScope           of qsymbol
  | NoWP
  | FilterMatchFailure
  | LvMapOnNonAssign

exception TyError of EcLocation.t * env * tyerror

(* issue a type error for a type or expression *)

val tyerror : EcLocation.t -> env -> tyerror -> 'a

(* given an environment and unification environment, and a location
   for error messages, try to unify a type with an expected type
   (modifying the unification environment) *)

val unify_or_fail :
  env -> EcUnify.unienv -> EcLocation.t -> expct:ty -> ty -> unit

type typolicy  (* type policies *)

val tp_relax   : typolicy  (* allows both "_" and type variables *)
val tp_nothing : typolicy  (* allows neither "_" nor type variables *)

(* given an environment and type policy, translate a type from
   concrete to abstract syntax (modifying the unification environment)
   *)

val transty : typolicy -> env -> EcUnify.unienv -> pty -> ty

(* given an environment and type policy, translate a list of types
   from concrete to abstract syntax (modifying the unification
   environment) *)

val transtys :
  typolicy -> env -> EcUnify.unienv -> pty list -> ty list

(* given an environment and unification environment, translate instantiation
   of type variables (modifying the unification environment) *)

val transtvi : env -> EcUnify.unienv -> ptyannot -> EcUnify.tvar_inst

(* given an environment and unification environment, translate an
   expression from concrete to abstract syntax, yielding an abstract
   type (modifying the unification environment) *)

val transexp :
  env -> EcUnify.unienv -> pexpr -> expr * ty

(* given an environment, unification environment and expected type,
   translate an expression from concrete to abstract syntax (modifying
   the unification environment) *)

val transexpcast :
  env -> EcUnify.unienv -> ty -> pexpr -> expr
