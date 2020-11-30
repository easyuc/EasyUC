(* Module UcTypecheckTypesExpr *)

(* Adapted from src/ecTyping.ml of the EasyCrypt distribution, which
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
open EcPath
open EcMaps
open EcSymbols
open EcLocation
open EcTypes
open EcModules
open EcDecl
open EcFol
open UcSpec

module MMsym = EcSymbols.MMsym
module Sid   = EcIdent.Sid
module Mid   = EcIdent.Mid

module EqTest = EcReduction.EqTest
module NormMp = EcEnv.NormMp

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
  | MAE_WrongArgCount       of int * int  (* expected, got *)
  | MAE_InvalidArgType      of EcPath.mpath * tymod_cnv_failure
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

exception TyError of EcLocation.t * EcEnv.env * tyerror

let tyerror loc env e = raise (TyError (loc, env, e))

type restriction_who =
  | RW_mod of EcPath.mpath
  | RW_fun of EcPath.xpath

type restriction_err =
  | RE_UseVariable          of EcPath.xpath
  | RE_UseVariableViaModule of EcPath.xpath * EcPath.mpath
  | RE_UseModule            of EcPath.mpath
  | RE_VMissingRestriction  of EcPath.xpath * EcPath.mpath pair
  | RE_MMissingRestriction  of EcPath.mpath * EcPath.mpath pair

type restriction_error = restriction_who * restriction_err

exception RestrictionError of EcEnv.env * restriction_error

let ident_of_osymbol x =
  omap unloc x |> odfl "_" |> EcIdent.create

module UE = EcUnify.UniEnv

let unify_or_fail (env : EcEnv.env) ue loc ~expct:ty1 ty2 =
  try  EcUnify.unify env ue ty1 ty2
  with EcUnify.UnificationFailure pb ->
    match pb with
    | `TyUni (t1, t2)->
        let tyinst = Tuni.offun (UE.assubst ue) in
          tyerror loc env (TypeMismatch ((tyinst ty1, tyinst ty2),
                                         (tyinst  t1, tyinst  t2)))
    | `TcCtt _ ->
        tyerror loc env TypeClassMismatch

let select_local env (qs,s) =
  if   qs = []
  then EcEnv.Var.lookup_local_opt s env
  else None

let select_pv env side name ue tvi psig =
  if   tvi <> None
  then []
  else
    try
      let pvs = EcEnv.Var.lookup_progvar ?side name env in
      let select (pv,ty) =
        let subue = UE.copy ue in
        let texpected = EcUnify.tfun_expected subue psig in
          try
            EcUnify.unify env subue ty texpected;
            [(pv, ty, subue)]
          with EcUnify.UnificationFailure _ -> []
      in
        select pvs
    with EcEnv.LookupFailure _ -> []

module OpSelect = struct
  type pvsel = [
    | `Proj of EcTypes.prog_var * EcTypes.ty * (int * int)
    | `Var  of EcTypes.prog_var
  ]

  type opsel = [
    | `Pv of EcMemory.memory option * pvsel
    | `Op of (EcPath.path * ty list)
    | `Lc of EcIdent.ident
    | `Nt of EcUnify.sbody
  ]

  type mode = [`Form | `Expr of [`InProc | `InOp]]

  type gopsel =
    opsel * EcTypes.ty * EcUnify.unienv * opmatch
end

let gen_select_op
    ~(actonly : bool)
    ~(mode    : OpSelect.mode)
    (opsc     : path option)
    (tvi      : EcUnify.tvi)
    (env      : EcEnv.env)
    (name     : EcSymbols.qsymbol)
    (ue       : EcUnify.unienv)
    (psig     : EcTypes.dom)

    : OpSelect.gopsel list =

  let fpv me (pv, ty, ue) =
    (`Pv (me, pv), ty, ue, (pv :> opmatch))

  and fop (op, ty, ue, bd) =
    match bd with
    | None -> (`Op op, ty, ue, (`Op op :> opmatch))
    | Some bd -> (`Nt bd, ty, ue, (`Op op :> opmatch))

  and flc (lc, ty, ue) =
    (`Lc lc, ty, ue, (`Lc lc :> opmatch)) in

  let ue_filter =
    match mode with
    | `Expr _ -> fun op -> not (EcDecl.is_pred op)
    | `Form   -> fun _  -> true
  in

  let by_scope opsc ((p, _), _, _, _) =
    EcPath.p_equal opsc (oget (EcPath.prefix p))

  and by_current ((p, _), _, _, _) =
    EcPath.isprefix (oget (EcPath.prefix p)) (EcEnv.root env)

  and by_tc ((p, _), _, _, _) =
    match oget (EcEnv.Op.by_path_opt p env) with
    | { op_kind = OB_oper (Some OP_TC) } -> false
    | _ -> true

  in

  match (if tvi = None then select_local env name else None) with
  | Some (id, ty) ->
     [ flc (id, ty, ue) ]

  | None ->
      let ops () =
        let ops = EcUnify.select_op ~filter:ue_filter tvi env name ue psig in
        let ops =
          opsc |> ofold (fun opsc -> List.mbfilter (by_scope opsc)) ops in
        let ops =
          match List.mbfilter by_current ops with [] -> ops | ops -> ops in
        let ops = match List.mbfilter by_tc ops with [] -> ops | ops -> ops in
        (List.map fop ops)

      and pvs () =
        let me, pvs =
          match EcEnv.Memory.get_active env, actonly with
          | None, true -> (None, [])
          | me  , _    -> (  me, select_pv env me name ue tvi psig)
        in List.map (fpv me) pvs
      in

      match mode with
      | `Expr `InOp   -> ops ()
      | `Form         -> (match pvs () with [] -> ops () | pvs -> pvs)
      | `Expr `InProc -> (match pvs () with [] -> ops () | pvs -> pvs)

let select_exp_op env mode opsc name ue tvi psig =
  gen_select_op ~actonly:false ~mode:(`Expr mode)
    opsc tvi env name ue psig

let select_form_op env opsc name ue tvi psig =
  gen_select_op ~actonly:true ~mode:`Form
    opsc tvi env name ue psig

let select_proj env opsc name ue tvi recty =
  let filter = (fun op -> EcDecl.is_proj op) in
  let ops = EcUnify.select_op ~filter tvi env name ue [recty] in
  let ops = List.map (fun (p, ty, ue, _) -> (p, ty, ue)) ops in

  match ops, opsc with
  | _ :: _ :: _, Some opsc ->
      List.filter
        (fun ((p, _), _, _) ->
          EcPath.p_equal opsc (oget (EcPath.prefix p)))
        ops

  | _, _ -> ops

let lookup_scope env popsc =
  match unloc popsc with
  | ([], x) when x = EcCoreLib.i_top -> EcCoreLib.p_top
  | _ -> begin
    match EcEnv.Theory.lookup_opt (unloc popsc) env with
    | None -> tyerror popsc.pl_loc env (UnknownScope (unloc popsc))
    | Some opsc -> fst opsc
  end

type typolicy = {
  tp_uni  : bool;   (* "_" (Tuniar) allowed  *)
  tp_tvar : bool;   (* type variable allowed *)
}

let tp_tydecl  = { tp_uni = false; tp_tvar = true ; } (* type decl. *)
let tp_relax   = { tp_uni = true ; tp_tvar = true ; } (* ops/forms/preds *)
let tp_nothing = { tp_uni = false; tp_tvar = false; } (* module type annot. *)
let tp_uni     = { tp_uni = true ; tp_tvar = false; } (* params/local vars. *)

type ismap = (instr list) Mstr.t

let transtcs (env : EcEnv.env) tcs =
  let for1 tc =
    match EcEnv.TypeClass.lookup_opt (unloc tc) env with
    | None -> tyerror tc.pl_loc env (UnknownTypeClass (unloc tc))
    | Some (p, _) -> p                  (* FIXME: TC HOOK *)
  in
    Sp.of_list (List.map for1 tcs)

let transtyvars (env : EcEnv.env) (loc, tparams) =
  let tparams = tparams |> omap
    (fun tparams ->
        let for1 ({ pl_desc = x }, tc) = (EcIdent.create x, transtcs env tc) in
          if not (List.is_unique (List.map (unloc |- fst) tparams)) then
            tyerror loc env DuplicatedTyVar;
          List.map for1 tparams)
  in
    EcUnify.UniEnv.create tparams

(* Types *)

let rec transty (tp : typolicy) (env : EcEnv.env) ue ty =
  match ty.pl_desc with
  | PTunivar ->
      if   tp.tp_uni
      then UE.fresh ue
      else tyerror ty.pl_loc env UniVarNotAllowed

  | PTvar s ->
      if tp.tp_tvar then
        try tvar (UE.getnamed ue s.pl_desc)
        with _ -> tyerror s.pl_loc env (UnboundTypeParameter s.pl_desc)
      else
        tyerror s.pl_loc env TypeVarNotAllowed;

  | PTtuple tys   ->
      ttuple (transtys tp env ue tys)

  | PTnamed { pl_desc = name } -> begin
      match EcEnv.Ty.lookup_opt name env with
      | None ->
          tyerror ty.pl_loc env (UnknownTypeName name)

      | Some (p, tydecl) ->
          if tydecl.tyd_params <> [] then begin
            let nargs = List.length tydecl.tyd_params in
              tyerror ty.pl_loc env (InvalidTypeAppl (name, nargs, 0))
          end;
          tconstr p []
      end

  | PTfun(ty1,ty2) ->
      tfun (transty tp env ue ty1) (transty tp env ue ty2)

  | PTapp ({ pl_desc = name }, tyargs) ->
    begin match EcEnv.Ty.lookup_opt name env with
    | None ->
      tyerror ty.pl_loc env (UnknownTypeName name)

    | Some (p, tydecl) ->
      let nargs    = List.length tyargs in
      let expected = List.length tydecl.tyd_params in

      if nargs <> expected then
        tyerror ty.pl_loc env (InvalidTypeAppl (name, expected, nargs));

      let tyargs = transtys tp env ue tyargs in
      tconstr p tyargs
    end

and transtys tp (env : EcEnv.env) ue tys =
  List.map (transty tp env ue) tys

let transty_for_decl env ty =
  let ue = UE.create (Some []) in
    transty tp_nothing env ue ty

(* Patterns *)

let transpattern1 env ue (p : plpattern) =
  match p.pl_desc with
  | LPSymbol { pl_desc = x } ->
      let ty = UE.fresh ue in
      let x  = EcIdent.create x in
      (LSymbol (x,ty), ty)

  | LPTuple xs ->
      let xs = unlocs xs in
      if not (List.is_unique xs) then
        tyerror p.pl_loc env NonLinearPattern
      else
        let xs     = List.map ident_of_osymbol xs in
        let subtys = List.map (fun _ -> UE.fresh ue) xs in
        (LTuple (List.combine xs subtys), ttuple subtys)

  | LPRecord fields ->
      let xs = List.map (unloc |- snd) fields in
      if not (List.is_unique xs) then
        tyerror p.pl_loc env NonLinearPattern;

      let fields =
        let for1 (name, v) =
          let filter = fun op -> EcDecl.is_proj op in
          let fds    = EcUnify.select_op ~filter None env (unloc name) ue [] in
            match List.ohead fds with
            | None ->
              let exn = UnknownRecFieldName (unloc name) in
                tyerror name.pl_loc env exn

            | Some ((fp, _tvi), opty, subue, _) ->
              let field = oget (EcEnv.Op.by_path_opt fp env) in
              let (recp, fieldidx, _) = EcDecl.operator_as_proj field in
                EcUnify.UniEnv.restore ~src:subue ~dst:ue;
                ((recp, fieldidx), opty, (name, v))
        in
          List.map for1 fields in

      let recp = Sp.of_list (List.map (fst |- proj3_1) fields) in
      let recp =
        match Sp.elements recp with
        | []        -> assert false
        | [recp]    -> recp
        | p1::p2::_ -> tyerror p.pl_loc env (MixingRecFields (p1, p2))
      in

      let recty  = oget (EcEnv.Ty.by_path_opt recp env) in
      let rec_   = snd (oget (EcDecl.tydecl_as_record recty)) in
      let reccty = tconstr recp (List.map (tvar |- fst) recty.tyd_params) in
      let reccty, rectvi =
        EcUnify.UniEnv.openty ue recty.tyd_params None reccty in
      let fields =
        List.fold_left
          (fun map (((_, idx), _, _) as field) ->
             if Mint.mem idx map then
               let name = fst (List.nth rec_ idx) in
               let exn  = DuplicatedRecFieldName name in
                 tyerror p.pl_loc env exn
             else
               Mint.add idx field map)
          Mint.empty fields in

      let fields =
        List.init (List.length rec_)
          (fun i ->
            match Mint.find_opt i fields with
            | None ->
                let pty = EcUnify.UniEnv.fresh ue in
                let fty = snd (List.nth rec_ i) in
                let fty, _ =
                  EcUnify.UniEnv.openty ue recty.tyd_params
                    (Some (EcUnify.TVIunamed rectvi)) fty
                in
                  (try  EcUnify.unify env ue pty fty
                   with EcUnify.UnificationFailure _ -> assert false);
                  (None, pty)

            | Some (_, opty, (_, v)) ->
                let pty = EcUnify.UniEnv.fresh ue in
                (try  EcUnify.unify env ue (tfun reccty pty) opty
                 with EcUnify.UnificationFailure _ -> assert false);
                (Some (EcIdent.create (unloc v)), pty))
      in
        (LRecord (recp, fields), reccty)

let transpattern env ue (p : plpattern) =
  match transpattern1 env ue p with
  | (LSymbol (x, ty)) as p, _ ->
      (EcEnv.Var.bind_local x ty env, p, ty)

  | LTuple xs as p, ty ->
      (EcEnv.Var.bind_locals xs env, p, ty)

  | LRecord (_, xs) as p, ty ->
      let xs = List.pmap (function
        | (None, _)    -> None
        | (Some x, ty) -> Some (x, ty)) xs
      in
        (EcEnv.Var.bind_locals xs env, p, ty)

let transtvi env ue tvi =
  match tvi.pl_desc with
  | TVIunamed lt ->
      EcUnify.TVIunamed (List.map (transty tp_relax env ue) lt)

  | TVInamed lst ->
      let add locals (s, t) =
        if List.exists (fun (s', _) -> unloc s = unloc s') locals then
          tyerror tvi.pl_loc env DuplicatedTyVar;
        (s, transty tp_relax env ue t) :: locals
      in

      let lst = List.fold_left add [] lst in
        EcUnify.TVInamed (List.rev_map (fun (s,t) -> unloc s, t) lst)

let rec destr_tfun env ue tf =
  match tf.ty_node with
  | Tunivar id -> begin
      let tf' = UE.repr ue tf in
        match tf == tf' with
        | false -> destr_tfun env ue tf'
        | true  ->
            let ty1 = UE.fresh ue in
            let ty2 = UE.fresh ue in
              EcUnify.unify env ue (tuni id) (tfun ty1 ty2);
              Some (ty1, ty2)
  end

  | Tfun (ty1, ty2) -> Some (ty1, ty2)

  | Tconstr (p, tys) when EcEnv.Ty.defined p env ->
      destr_tfun env ue (EcEnv.Ty.unfold p tys env)

  | _ -> None

let rec ty_fun_app loc env ue tf targs =
  match targs with
  | [] -> tf
  | t1 :: targs -> begin
      match destr_tfun env ue tf with
      | None -> tyerror loc env NotAFunction
      | Some (dom, codom) ->
        unify_or_fail env ue t1.pl_loc ~expct:dom t1.pl_desc;
        let loc = EcLocation.merge loc t1.pl_loc in
        ty_fun_app loc env ue codom targs
  end

let trans_binding env ue bd =
  let trans_bd1 env (xs, pty) =
    let ty  = transty tp_relax env ue pty in
    let xs  = List.map (fun x -> ident_of_osymbol (unloc x), ty) xs in
    let env = EcEnv.Var.bind_locals xs env in
    env, xs in
  let env, bd = List.map_fold trans_bd1 env bd in
  let bd = List.flatten bd in
  env, bd

let trans_record env ue (subtt, proj) (loc, b, fields) =
  let fields =
    let for1 rf =
      let filter = fun op -> EcDecl.is_proj op in
      let tvi    = rf.rf_tvi |> omap (transtvi env ue) in
      let fds    = EcUnify.select_op ~filter tvi env (unloc rf.rf_name) ue [] in
        match List.ohead fds with
        | None ->
            let exn = UnknownRecFieldName (unloc rf.rf_name) in
              tyerror rf.rf_name.pl_loc env exn

        | Some ((fp, _tvi), opty, subue, _) ->
            let field = oget (EcEnv.Op.by_path_opt fp env) in
            let (recp, fieldidx, _) = EcDecl.operator_as_proj field in
              EcUnify.UniEnv.restore ~src:subue ~dst:ue;
              ((recp, fieldidx), opty, rf)
    in
      List.map for1 fields in

  let recp = Sp.of_list (List.map (fst |- proj3_1) fields) in
  let recp =
    match Sp.elements recp with
    | []        -> assert false
    | [recp]    -> recp
    | p1::p2::_ -> tyerror loc env (MixingRecFields (p1, p2))
  in

  let recty  = oget (EcEnv.Ty.by_path_opt recp env) in
  let rec_   = snd (oget (EcDecl.tydecl_as_record recty)) in
  let reccty = tconstr recp (List.map (tvar |- fst) recty.tyd_params) in
  let reccty, rtvi = EcUnify.UniEnv.openty ue recty.tyd_params None reccty in
  let tysopn = Tvar.init (List.map fst recty.tyd_params) rtvi in

  let fields =
    List.fold_left
      (fun map (((_, idx), _, _) as field) ->
         if Mint.mem idx map then
           let name = fst (List.nth rec_ idx) in
           let exn  = DuplicatedRecFieldName name in
           tyerror loc env exn
         else
           Mint.add idx field map)
      Mint.empty fields in

  let dflrec =
    let doit f =
      let (dfl, dflty) = subtt f in
      unify_or_fail env ue f.pl_loc ~expct:reccty dflty; dfl
    in b |> omap doit
  in

  let fields =
    let get_field i name rty =
      match Mint.find_opt i fields with
      | Some (_, opty, rf) ->
          `Set (opty, rf.rf_value)

      | None ->
          match dflrec with
          | None   -> tyerror loc env (MissingRecField name)
          | Some _ -> `Dfl (Tvar.subst tysopn rty, name)
    in List.mapi (fun i (name, rty) -> get_field i name rty) rec_
  in

  let fields =
    let for1 = function
      | `Set (opty, value) ->
          let pty = EcUnify.UniEnv.fresh ue in
          (try  EcUnify.unify env ue (tfun reccty pty) opty
           with EcUnify.UnificationFailure _ -> assert false);
          let e, ety = subtt value in
          unify_or_fail env ue value.pl_loc ~expct:pty ety;
          (e, pty)

      | `Dfl (rty, name) ->
          let nm = oget (EcPath.prefix recp) in
          (proj (nm, name, (rtvi, reccty), rty, oget dflrec), rty)

    in
      List.map for1 fields
  in

  let ctor =
    EcPath.pqoname
      (EcPath.prefix recp)
      (Printf.sprintf "mk_%s" (EcPath.basename recp))
  in
    (ctor, fields, (rtvi, reccty))

let trans_branch ~loc env ue gindty ((pb, body) : ppattern * _) =
  let filter = fun op -> EcDecl.is_ctor op in
  let PPApp ((cname, tvi), cargs) = pb in
  let tvi = tvi |> omap (transtvi env ue) in
  let cts = EcUnify.select_op ~filter tvi env (unloc cname) ue [] in

  match cts with
  | [] ->
      tyerror cname.pl_loc env (InvalidMatch FXE_CtorUnk)

  | _ :: _ :: _ ->
      tyerror cname.pl_loc env (InvalidMatch FXE_CtorAmbiguous)

  | [(cp, tvi), opty, subue, _] ->
      let ctor = oget (EcEnv.Op.by_path_opt cp env) in
      let (indp, ctoridx) = EcDecl.operator_as_ctor ctor in
      let indty = oget (EcEnv.Ty.by_path_opt indp env) in
      let ind = (oget (EcDecl.tydecl_as_datatype indty)).tydt_ctors in
      let ctorsym, ctorty = List.nth ind ctoridx in

      let args_exp = List.length ctorty in
      let args_got = List.length cargs in

      if args_exp <> args_got then begin
        tyerror cname.pl_loc env (InvalidMatch
          (FXE_CtorInvalidArity (snd (unloc cname), args_exp, args_got)))
      end;

      let cargs_lin = List.pmap (fun o -> omap unloc (unloc o)) cargs in

      if not (List.is_unique cargs_lin) then
        tyerror cname.pl_loc env (InvalidMatch FXE_MatchNonLinear);

      EcUnify.UniEnv.restore ~src:subue ~dst:ue;

      let ctorty =
        let tvi = Some (EcUnify.TVIunamed tvi) in
          fst (EcUnify.UniEnv.opentys ue indty.tyd_params tvi ctorty) in
      let pty = EcUnify.UniEnv.fresh ue in

      (try  EcUnify.unify env ue (toarrow ctorty pty) opty
       with EcUnify.UnificationFailure _ -> assert false);
      unify_or_fail env ue loc pty gindty;

      let create o = EcIdent.create (omap_dfl unloc "_" o) in
      let pvars = List.map (create |- unloc) cargs in
      let pvars = List.combine pvars ctorty in

      (ctorsym, (pvars, body))

let trans_match ~loc env ue (gindty, gind) pbs =
  let pbs = List.map (trans_branch ~loc env ue gindty) pbs in

  if List.length pbs < List.length gind.tydt_ctors then
    tyerror loc env (InvalidMatch FXE_MatchPartial);

  if List.length pbs > List.length gind.tydt_ctors then
    tyerror loc env (InvalidMatch FXE_MatchDupBranches);

  let pbs = Msym.of_list pbs in

  List.map
    (fun (x, _) -> oget (Msym.find_opt x pbs))
    gind.tydt_ctors

let trans_if_match ~loc env ue (gindty, gind) (c, b1, b2) =
  let (c, (cargs, b1)) = trans_branch ~loc env ue gindty (c, b1) in

  List.map
    (fun (x, xargs) ->
      if   sym_equal c x
      then (cargs, Some b1)
      else (List.map (fun ty -> (EcIdent.create "_", ty)) xargs), b2)
    gind.tydt_ctors

let expr_of_opselect
  (env, ue) loc ((sel, ty, subue, _) : OpSelect.gopsel) args =
  EcUnify.UniEnv.restore ~src:subue ~dst:ue;

  let esig  = List.map (lmap snd) args in
  let args  = List.map (fst |- unloc) args in
  let codom = ty_fun_app loc env ue ty esig in

  let op, args =
    match sel with
    | `Nt (lazy (bds, body)) ->
         let nbds  = List.length bds in
         let nargs = List.length args in

         let ((tosub, args), elam) =
           if nbds <= nargs then
             (List.split_at nbds args, [])
           else
             let xs = snd (List.split_at nargs bds) in
             let xs = List.map (fst_map EcIdent.fresh) xs in
             ((args @ List.map (curry e_local) xs, []), xs) in
         let lcmap = List.map2 (fun (x, _) y -> (x, y)) bds tosub in
         let subst = { EcTypes.e_subst_id with es_freshen = true; } in
         let subst = { subst with es_loc = Mid.of_list lcmap; } in
         let body  = EcTypes.e_subst subst body in
         (e_lam elam body, args)

    | (`Op _ | `Lc _ | `Pv _) as sel -> let op = match sel with
      | `Op (p, tys) -> e_op p tys ty
      | `Lc id       -> e_local id ty

      | `Pv (_me, `Var   pv)               -> e_var pv ty
      | `Pv (_me, `Proj (pv, _  , (0, 1))) -> e_var pv ty
      | `Pv (_me, `Proj (pv, ty', (i, _))) -> e_proj (e_var pv ty') i ty

    in (op, args)

  in (e_app op args codom, codom)

let transexp (env : EcEnv.env) ue e =
  let mode = `InOp in
  let rec transexp_r (osc : EcPath.path option) (env : EcEnv.env) (e : pexpr) =
    let loc = e.pl_loc in
    let transexp = transexp_r osc in

    match e.pl_desc with
    | PEcast (pe, pty) ->
        let ty = transty tp_relax env ue pty in
        let (_, ety) as aout = transexp env pe in
        unify_or_fail env ue pe.pl_loc ~expct:ty ety; aout

    | PEint i ->
        (e_int i, tint)

    | PEdecimal (n, f) ->
        (e_decimal (n, f), treal)

    | PEident ({ pl_desc = name }, tvi) ->
        let tvi = tvi |> omap (transtvi env ue) in
        let ops = select_exp_op env mode osc name ue tvi [] in
        begin match ops with
        | [] -> tyerror loc env (UnknownVarOrOp (name, []))

        | [sel] ->
            expr_of_opselect (env, ue) e.pl_loc sel []

        | _ ->
          let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
          tyerror loc env (MultipleOpMatch (name, [], matches))
        end

    | PEscope (popsc, e) ->
        let opsc = lookup_scope env popsc in
          transexp_r (Some opsc) env e

    | PEapp
      ({ pl_desc = PEident({ pl_desc = name; pl_loc = loc }, tvi)}, pes) ->
        let tvi  = tvi |> omap (transtvi env ue) in
        let es   = List.map (transexp env) pes in
        let esig = snd (List.split es) in
        let ops  = select_exp_op env mode osc name ue tvi esig in
        begin match ops with
        | [] ->
            let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
            tyerror loc env (UnknownVarOrOp (name, esig))

        | [sel] ->
            let es = List.map2 (fun e l -> mk_loc l.pl_loc e) es pes in
            expr_of_opselect (env, ue) loc sel es

        | _ ->
            let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
            let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
            tyerror loc env (MultipleOpMatch (name, esig, matches))
        end

    | PEapp (pe, pes) ->
        let e, ty = transexp env pe in
        let es = List.map (transexp env) pes in
        let esig = List.map2 (fun (_, ty) l -> mk_loc l.pl_loc ty) es pes in
        let codom = ty_fun_app pe.pl_loc env ue ty esig in
          (e_app e (List.map fst es) codom, codom)

    | PElet (p, (pe1, paty), pe2) ->
        let (penv, pt, pty) = transpattern env ue p in
        let aty = paty |> omap (transty tp_relax env ue) in

        let e1, ty1 = transexp env pe1 in
        unify_or_fail env ue pe1.pl_loc ~expct:pty ty1;
        aty |>
        oiter (fun aty -> unify_or_fail env ue pe1.pl_loc ~expct:aty ty1);

        let e2, ty2 = transexp penv pe2 in
        (e_let pt e1 e2, ty2)

    | PEtuple es -> begin
        let tes = List.map (transexp env) es in

        match tes with
        | []      -> (e_tt, EcTypes.tunit)
        | [e, ty] -> (e, ty)
        | _       ->
            let es, tys = List.split tes in
              (e_tuple es, ttuple tys)
    end

    | PEif (pc, pe1, pe2) ->
        let c, tyc = transexp env pc in
        let e1, ty1 = transexp env pe1 in
        let e2, ty2 = transexp env pe2 in
        unify_or_fail env ue pc .pl_loc ~expct:tbool tyc;
        unify_or_fail env ue pe2.pl_loc ~expct:ty1   ty2;
        (e_if c e1 e2, ty1)

    | PEmatch (pce, pb) ->
        let ce, ety = transexp env pce in
        let ety = Tuni.offun (EcUnify.UniEnv.assubst ue) ety in
        let inddecl =
          match (EcEnv.ty_hnorm ety env).ty_node with
          | Tconstr (indp, _) -> begin
              match EcEnv.Ty.by_path indp env with
              | { tyd_type = `Datatype dt } ->
                    Some (indp, dt)
              | _ -> None
            end
          | _ -> None in

        let (_indp, inddecl) =
          match inddecl with
          | None   -> tyerror pce.pl_loc env NotAnInductive
          | Some x -> x in

        let branches =
          trans_match ~loc:e.pl_loc env ue (ety, inddecl) pb in

        let branches, bty = List.split (List.map (fun (lcs, s) ->
          let env  = EcEnv.Var.bind_locals lcs env in
          let bdy  = transexp env s in
          e_lam lcs (fst bdy), (snd bdy, s.pl_loc)) branches) in

        let rty = EcUnify.UniEnv.fresh ue in

        List.iter (fun (ty, loc) -> unify_or_fail env ue loc ~expct:ty rty) bty;
        e_match ce branches rty, rty

    | PEforall (xs, pe) ->
        let env, xs = trans_binding env ue xs in
        let e, ety = transexp env pe in
        unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
        (e_forall xs e, tbool)

    | PEexists (xs, pe) ->
        let env, xs = trans_binding env ue xs in
        let e, ety = transexp env pe in
        unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
        (e_exists xs e, tbool)

    | PElambda (bd, pe) ->
        let env, xs = trans_binding env ue bd in
        let e, ty = transexp env pe in
        let ty = toarrow (List.map snd xs) ty in
        (e_lam xs e, ty)

    | PErecord (b, fields) ->
        let (ctor, fields, (rtvi, reccty)) =
          let proj (recp, name, (rtvi, reccty), pty, arg) =
            let proj = EcPath.pqname recp name in
            let proj = e_op proj rtvi (tfun reccty pty) in
            e_app proj [arg] pty
          in trans_record env ue (transexp env, proj) (loc, b, fields) in
        let ctor = e_op ctor rtvi (toarrow (List.map snd fields) reccty) in
        let ctor = e_app ctor (List.map fst fields) reccty in
          ctor, reccty

    | PEproj (sube, x) -> begin
      let sube, ety = transexp env sube in
      match select_proj env osc (unloc x) ue None ety with
      | [] ->
        let ty = Tuni.offun (EcUnify.UniEnv.assubst ue) ety in
        let me = EcFol.mhr in
        let mp =
          match ty.ty_node with
          | Tglob mp -> mp
          | _ -> tyerror x.pl_loc env (UnknownProj (unloc x)) in
        let f = NormMp.norm_glob env me mp in
        let lf =
          match f.f_node with
          | Ftuple l -> l
          | _ -> tyerror x.pl_loc env (UnknownProj (unloc x)) in
        let vx,ty =
          match EcEnv.Var.lookup_progvar_opt ~side:me (unloc x) env with
          | None -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, []))
          | Some (x1, ty) ->
              match x1 with
              | `Var x -> NormMp.norm_pvar env x, ty
              | _ -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, [])) in
        let find f1 =
           match f1.f_node with
            | Fpvar (x1, _) -> EcTypes.pv_equal vx (NormMp.norm_pvar env x1)
            | _ -> false in
        let i =
          match List.oindex find lf with
          | None -> tyerror x.pl_loc env (UnknownProj (unloc x))
          | Some i -> i in
        e_proj sube i ty, ty


      | _::_::_ ->
         tyerror x.pl_loc env (AmbiguousProj (unloc x))

      | [(op, tvi), pty, subue] ->
        EcUnify.UniEnv.restore ~src:subue ~dst:ue;
        let rty = EcUnify.UniEnv.fresh ue in
        (try  EcUnify.unify env ue (tfun ety rty) pty
         with EcUnify.UnificationFailure _ -> assert false);
        (e_app (e_op op tvi pty) [sube] rty, rty)
    end

    | PEproji (sube, i) -> begin
      let sube', ety = transexp env sube in
      let ty = Tuni.offun (EcUnify.UniEnv.assubst ue) ety in
      match (EcEnv.ty_hnorm ty env).ty_node with
      | Ttuple l when i < List.length l ->
        let ty = List.nth l i in
        e_proj sube' i ty, ty
      | _ -> tyerror sube.pl_loc env (AmbiguousProji(i,ty))
    end

  in
    transexp_r None env e

let transexpcast (env : EcEnv.env) ue t e =
  let (e', t') = transexp env ue e in
    unify_or_fail env ue e.pl_loc ~expct:t t'; e'
