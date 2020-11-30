(* UcTypesExprsErrorMessages module *)

(* Formatting error messages issued when translating types and
   expressions *)

(* adapted from ecUserMessages.ml of EasyCrypt distribution *)

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

open EcSymbols
open EcUid
open EcUtils
open EcTypes
open UcTransTypesExprs

let pp_fxerror _env fmt error =
  let msg x = Format.fprintf fmt x in

  match error with
  | FXE_EmptyMatch ->
      msg "this pattern matching has no clauses"

  | FXE_MatchParamsMixed ->
      msg "this pattern matching matches on different parameters"

  | FXE_MatchParamsDup ->
      msg "this pattern matching matches a parameter twice"

  | FXE_MatchParamsUnk ->
      msg "this pattern matching matches an unbound parameter"

  | FXE_MatchNonLinear ->
      msg "this pattern is non-linear"

  | FXE_MatchDupBranches ->
      msg "redundant clauses"

  | FXE_MatchPartial ->
      msg "non-exhaustive clauses"

  | FXE_CtorUnk ->
      msg "unknown constructor name"

  | FXE_CtorAmbiguous ->
      msg "ambiguous constructor name"

  | FXE_CtorInvalidArity (cname, i, j) ->
      msg
        "the constructor %s expects %d argument(s) (%d argument(s) given)"
        cname i j

let pp_tyerror env1 fmt error =
  let env   = EcPrinting.PPEnv.ofenv env1 in
  let msg x = Format.fprintf fmt x in
  let pp_type fmt ty = EcPrinting.pp_type env fmt ty in

  match error with
  | UniVarNotAllowed ->
      msg "type place holders not allowed"

  | TypeVarNotAllowed ->
      msg "type variables not allowed"

  | UnboundTypeParameter x ->
      msg "unbound type parameter: %s" x

  | UnknownTypeName qs ->
      msg "unknown type name: %a" pp_qsymbol qs

  | UnknownTypeClass qs ->
      msg "unknown type class: %a" pp_qsymbol qs

  | UnknownRecFieldName qs ->
      msg "unknown (record) field name: %a" pp_qsymbol qs

  | DuplicatedRecFieldName qs ->
      msg "duplicated (record) field name: %s" qs

  | MissingRecField qs ->
      msg "missing (record) field: %s" qs

  | MixingRecFields (p1, p2) ->
      msg "mixing (record) fields from different record types: %a / %a"
        (EcPrinting.pp_tyname env) p1
        (EcPrinting.pp_tyname env) p2

  | UnknownProj qs ->
      msg "unknown record projection: %a" pp_qsymbol qs

  | AmbiguousProj qs ->
      msg "ambiguous record projection: %a" pp_qsymbol qs

  | AmbiguousProji (i, ty) ->
    let i = max (i + 1) 2 in
    msg "type %a should be a tuple of at least %i elements" pp_type ty i

  | InvalidTypeAppl (name, _, _) ->
      msg "invalid type application: %a" pp_qsymbol name

  | DuplicatedTyVar ->
      msg "a type variable appear at least twice"

  | DuplicatedField name ->
      msg "duplicated field name: `%s'" name

  | NonLinearPattern ->
      msg "non-linear pattern matching"

  | TypeMismatch ((ty1, ty2), _) ->
      msg "This expression has type@\n";
      msg "  @[<hov 2> %a@]@\n@\n" pp_type ty2;
      msg "but is expected to have type@\n";
      msg "  @[<hov 2> %a@]" pp_type ty1

  | TypeClassMismatch ->
      msg "Type-class unification failure"

  | NotAFunction ->
      msg "the expression is not a function, it can not be applied"

  | NotAnInductive ->
      msg "the expression does not have an inductive type"

  | UnknownVarOrOp (name, []) ->
      (match name with
       | ([], symbol) ->
           if String.starts_with symbol "intport:"
           then msg "invalid internal port name: `%a'"
                pp_symbol (String.lchop ~n:(String.length "intport:") symbol)
           else msg "unknown identifer: `%a'"
                pp_symbol symbol
       | _            ->
         msg "unknown qualified identifier: `%a'" pp_qsymbol name)

  | UnknownVarOrOp (name, tys) ->
      msg "no matching operator, named `%a', " pp_qsymbol name;
      msg "for the following parameters' type:@\n";
      List.iteri (fun i ty -> msg "  [%d]: @[%a@]@\n" (i+1) pp_type ty) tys

  | MultipleOpMatch (name, tys, matches) -> begin
      let uvars = List.map EcTypes.Tuni.univars tys in
      let uvars = List.fold_left Suid.union Suid.empty uvars in

      begin match tys with
      | [] ->
          msg
            "more that one variable or constant matches `%a'@\n"
            pp_qsymbol name

      | _  ->
          let pp_argty i ty = msg "  [%d]: @[%a@]@\n" (i+1) pp_type ty in
          msg "more than one operator, named `%a', matches.@\n@\n"
          pp_qsymbol name;
          msg "operator parameters' type were:@\n";
          List.iteri pp_argty tys
      end;
      msg "@\n";

      let pp_op fmt ((op, inst), subue) =
        let inst = Tuni.offun_dom (EcUnify.UniEnv.assubst subue) inst in

        begin match inst with
        | [] ->
            Format.fprintf fmt "%a"
              EcPrinting.pp_path op
        | _  ->
          Format.fprintf fmt "%a <%a>"
            EcPrinting.pp_path op
            (EcPrinting.pp_list ",@ " pp_type) inst
        end;

        let myuvars = List.map EcTypes.Tuni.univars inst in
        let myuvars = List.fold_left Suid.union uvars myuvars in
        let myuvars = Suid.elements myuvars in

        let tysubst = Tuni.offun (EcUnify.UniEnv.assubst subue) in
        let myuvars = List.pmap
          (fun uid ->
            match tysubst (tuni uid) with
            | { ty_node = Tunivar uid' } when uid = uid' -> None
            | ty -> Some (uid, ty))
          myuvars
        in

        if not (List.is_empty myuvars) then begin
          Format.fprintf fmt "@\n    where@\n";
          List.iter (fun (uid, uidty) ->
            Format.fprintf fmt "      %a = %a@\n"
              (EcPrinting.pp_tyunivar env) uid pp_type uidty)
            myuvars
        end
      in

      msg "the list of matching objects follows:@\n";
      List.iter (fun (m, ue) ->
        let (title, Cb (x, pp)) =
          match m with
          | `Var pv ->
             ("prog. variable", Cb (pv, EcPrinting.pp_pv env))
          | `Lc id ->
             ("local variable", Cb (id, EcPrinting.pp_local env))
          | `Proj (pv, _, _) ->
             ("variable proj.", Cb (pv, EcPrinting.pp_pv env))
          | `Op op ->
             ("operator", Cb ((op, ue), pp_op))
        in msg "  [%s]: %a@\n" title pp x) matches
  end

  | InvalidMatch fxerror ->
      pp_fxerror env1 fmt fxerror

  | PatternNotAllowed ->
      msg "pattern not allowed here"

  | UnknownScope sc ->
      msg "unknown scope: `%a'" pp_qsymbol sc
