(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcLocation
open EcTypes
open EcCoreSubst
open EcParsetree
open EcDecl

module TT = EcTyping

(* -------------------------------------------------------------------- *)
type tperror =
| TPE_Typing of EcTyping.tyerror
| TPE_TyNotClosed
| TPE_DuplicatedConstr of symbol

exception TransPredError of EcLocation.t * EcEnv.env * tperror

let tperror loc env e = raise (TransPredError (loc, env, e))

(* -------------------------------------------------------------------- *)
let close_pr_body (uni : ty EcUid.Muid.t) (body : prbody) =
  let fsubst = EcFol.Fsubst.f_subst_init ~tu:uni () in
  let tsubst = ty_subst fsubst in

  match body with
  | PR_Plain body ->
     PR_Plain (Fsubst.f_subst fsubst body)

  | PR_Ind pri ->
     let for1 ctor =
       { prc_ctor = ctor.prc_ctor;
         prc_bds  = List.map (snd_map (Fsubst.gty_subst fsubst)) ctor.prc_bds;
         prc_spec = List.map (Fsubst.f_subst fsubst) ctor.prc_spec; } in
     PR_Ind
       { pri_args  = List.map (snd_map tsubst) pri.pri_args;
         pri_ctors = List.map for1 pri.pri_ctors; }

(* -------------------------------------------------------------------- *)
let trans_preddecl_r (env : EcEnv.env) (pr : ppredicate located) =
  let pr = pr.pl_desc and loc = pr.pl_loc in
  let ue = TT.transtyvars env (loc, pr.pp_tyvars) in
  let tp = TT.tp_relax in

  let dom, body =
    match pr.pp_def with
    | PPabstr ptys ->
        (List.map (TT.transty tp env ue) ptys, None)

    | PPconcr (bd, pe) ->
        let env, xs = TT.trans_binding env ue bd in
        let body = TT.trans_prop env ue pe in
        let dom = List.map snd xs in
        let xs = List.map (fun (x,ty) -> x, EcAst.GTty ty) xs in
        let lam = EcFol.f_lambda xs body in
        (dom, Some (PR_Plain lam))

    | PPind (bd, pi) ->
        Msym.odup unloc (List.map (fun c -> c.pic_name) pi) |>
          oiter (fun (_, x) ->
            tperror x.pl_loc env (TPE_DuplicatedConstr (unloc x)));

        let env, xs = TT.trans_binding env ue bd in

        let for1 ctor =
          let env, bs = TT.trans_gbinding env ue ctor.pic_bds in
          let fs = List.map (TT.trans_prop env ue) ctor.pic_spec in
          { prc_ctor = unloc ctor.pic_name;
            prc_bds  = bs; prc_spec = fs; } in

        let prind = { pri_args = xs; pri_ctors = List.map for1 pi; } in
        (List.map snd xs, Some (PR_Ind prind))

  in

  if not (EcUnify.UniEnv.closed ue) then
    tperror loc env TPE_TyNotClosed;

  let uidmap     = EcUnify.UniEnv.assubst ue in
  let tparams = EcUnify.UniEnv.tparams ue in
  let body    = body |> omap (close_pr_body uidmap) in

  let dom     = Tuni.subst_dom uidmap dom in

  EcDecl.mk_pred ~opaque:optransparent tparams dom body pr.pp_locality

(* -------------------------------------------------------------------- *)
let trans_preddecl (env : EcEnv.env) (pr : ppredicate located) =
  try  trans_preddecl_r env pr
  with TT.TyError (loc, env, e) -> tperror loc env (TPE_Typing e)
