open Yojson
open EcTyping

let parse_trans_type (env : EcEnv.env) (ty_str : string) : EcTypes.ty =
  let pty = EcParser.ty_start ty_str in
  let policy = UcTransTypesExprs.tp_nothing in
  let ue  = EcTyping.transtyvars env (EcLocation._dummy, None) in
  transty policy env ue pty

let parse_trans_frm (env : EcEnv.env) (frm_str : string) : EcTypes.ty =
  let pformula = EcParser.form_start frm_str in
  let policy = UcTransTypesExprs.tp_nothing in
  let ue  = EcTyping.transtyvars env (EcLocation._dummy, None) in
  trans_form_opt env ue None pformula

let json_hyps2ldecl_hyps (jhyps : string) : EcEnv.LDecl.hyps =
  let env = UcEcInterface.env () in
  let hyps = EcEnv.LDecl.init env [] in
  let json = Yojson.Safe.from_string jhyps in
  let hs =
    match json with
    | `List hs -> hs
    | _ -> failwith "bad json! A list of hypotheses is expected."
  in  
  let add_h_to_hyps hyps h : EcEnv.LDecl.hyps =
    match h with
    | `Assoc [(v_name,`String v_type)] ->
      let id = EcIdent.create v_name in
      let ty = parse_trans_type (EcEnv.LDecl.toenv hyps) v_type in
      let l_k = EcBaseLogic.LD_var (ty, None) in
      EcEnv.LDecl.add_local id l_k hyps
    | `String fs ->
      let f = parse_trans_frm (EcEnv.LDecl.toenv hyps) fs in
      let l_k = EcBaseLogic.LD_hyp f in
      let name = EcUid.NameGen.ofint (EcUid.unique ()) in
      let id = EcEnv.LDecl.fresh_id hyps name in
      EcEnv.LDecl.add_local id l_k hyps
    | _ -> failwith "bad json hyp! Only variable bindings in the form of {name_str : type_str} and formula strings allowed"
  in
  List.fold_left add_h_to_hyps hyps hs


let ldecl_hyps2json_hyps (lhyps : EcEnv.LDecl.hyps) : string =[]
