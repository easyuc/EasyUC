open UcTypedSpec
open EcTypes
open EcLocation
open UcMessage

(* params_map_to_list converts ty_index IdMap.t into a list of
name, type pairs. The list is ordered according to the index of ty_index *)
let params_map_to_list (pm : ty_index IdMap.t) : (string * EcTypes.ty) list =
  let bpm = IdMap.bindings pm in
  let bpm = List.map (fun (s,ti) -> (s, EcLocation.unloc ti)) bpm in
  let bpm_ord = List.sort (fun (_,(_,i1)) (_,(_,i2)) -> i1-i2) bpm in
  List.map (fun (name,(ty,_)) -> (name, ty)) bpm_ord

let _pi = "pi"

let abs_oper_int (name : string) : string = "op "^name^" : int."

let pi_op : string = abs_oper_int _pi

let uc_name (name : string) : string = "UC_"^name

let open_theory (name : string) : string = "theory "^name^"."

let close_theory (name : string) : string = "end "^name^"."

let print_newline (ppf : Format.formatter) : unit =
  Format.fprintf ppf "@."

let print_str_nl (ppf : Format.formatter) (str : string) : unit =
  Format.fprintf ppf "%s@." str;
  print_newline ppf

let name_record_func (msg_name : string) : string = msg_name^"__func"

let name_record_adv (msg_name : string) : string = msg_name^"__adv"

let name_record (msg_name : string) (param_name : string) : string = msg_name^"_"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)

let name_epdp_op (tyname : string) : string = "epdp_"^tyname^"_univ"


(* print epdp for message data ----------------------------------------------*)

(* epdp for constructed types -----------------------------------------------------*)

let epdp_opex_for_typath (ppf : Format.formatter) (sc : EcScope.scope)
(tp : EcPath.path) (tyl : ty list) : unit =
  let env = EcScope.env sc in
  let qtp = EcPath.toqsymbol tp in
  let qepdp = (fst qtp, name_epdp_op (snd qtp)) in
  let qbase = (["Top";"UCBasicTypes"], snd qepdp) in
  let pth, oper =
    match EcEnv.Op.lookup_opt qepdp env with
    | Some (pth, t) -> pth , t 
    | None -> match EcEnv.Op.lookup_opt qbase env with
              | Some (pth, t) -> pth , t 
              | None -> failure ("couldn't find epdp operator for "^
                          (EcPath.tostring tp))
                            (*TODO special case for univ_univ? or change epdp_id name?*)
                            (*TODO try to find epdp for given type in scope, if that fails, make tydecl analisys and try to construct epdp, if that fails throw exception*)
  in
  let epdp_opex = e_op pth tyl oper.op_ty in
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  Format.fprintf ppf "@[%a@]" (EcPrinting.pp_expr ppe) epdp_opex

(*---------------------------------------------------------------------------*)

(* epdp for tuples ----------------------------------------------------------*)
let epdp_basicUCtuple_name (arity : int) : string option =
  match arity with
  | 2 -> Some "epdp_pair_univ"
  | 3 -> Some "epdp_tuple3_univ"
  | 4 -> Some "epdp_tuple4_univ"
  | 5 -> Some "epdp_tuple5_univ"
  | 6 -> Some "epdp_tuple6_univ"
  | 7 -> Some "epdp_tuple7_univ"
  | 8 -> Some "epdp_tuple8_univ"
  | _ -> None

let epdp_opex_for_tuple (ppf : Format.formatter) (sc : EcScope.scope)
(tyl : ty list) : unit =
  match epdp_basicUCtuple_name (List.length tyl) with
  | Some name ->
     let qbase = (["Top";"UCBasicTypes"], name) in
     let env = EcScope.env sc in
     let pth,oper = EcEnv.Op.lookup qbase env in
     let epdp_opex = e_op pth tyl oper.op_ty in
     let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
     Format.fprintf ppf "@[%a@]" (EcPrinting.pp_expr ppe) epdp_opex
  | None -> failure "tuples must have between 2 and 8 members"


(*---------------------------------------------------------------------------*)

(* epdp for type applications -----------------------------------------------*)
let epdp_basicUCappty_name (tyname : EcSymbols.qsymbol) : string option =
  let epdp_name (name : string) : string option =
  match name with
    | "choice"  -> Some "epdp_choice_univ"
    | "choice3" -> Some "epdp_choice3_univ"
    | "choice4" -> Some "epdp_choice4_univ"
    | "choice5" -> Some "epdp_choice5_univ"
    | "choice6" -> Some "epdp_choice6_univ"
    | "choice7" -> Some "epdp_choice7_univ"
    | "choice8" -> Some "epdp_choice8_univ"
    | "option"  -> Some "epdp_option_univ"
    | "list"    -> Some "epdp_list_univ"
    | _ -> None
  in
  let qual,name = tyname in
  match qual with
  | ["Top";"UCBasicTypes"] -> epdp_name name
  | ["UCBasicTypes"] -> epdp_name name
  | [] -> epdp_name name
  | _ -> None

(*---------------------------------------------------------------------------*)

(* epdp for function types --------------------------------------------------*)

(*---------------------------------------------------------------------------*)

(* combining epdps to construct epdp for a type -----------------------------*)
let rec epdp_ty_univ_ex (sc : EcScope.scope) (ppf : Format.formatter) 
(t : ty) : unit  =
  match t.ty_node with
  | Ttuple  tys -> epdp_tuple_univ_ex sc ppf tys
  | Tconstr (pth, tys) -> epdp_constr_univ_ex sc ppf pth tys
  | Tfun (ty1, ty2) -> epdp_fun_univ_ex sc ppf ty1 ty2
  | _ -> failure ("Only tuples, constructed types, and functions are supported." )

and epdp_ptyl (ppf : Format.formatter) (sc : EcScope.scope)
(tl : ty list) : unit =
  List.iter ( fun t -> Format.fprintf ppf "@[@ (%a)@]"
     (epdp_ty_univ_ex sc) t
  ) tl
  
and epdp_tuple_univ_ex (sc : EcScope.scope) (ppf : Format.formatter) 
(tys : ty list) : unit =
  epdp_opex_for_tuple ppf sc tys;
  epdp_ptyl ppf sc tys

and epdp_constr_univ_ex (sc : EcScope.scope) (ppf : Format.formatter) 
(pth : EcPath.path) (tys : ty list) : unit =
  epdp_opex_for_typath ppf sc pth tys;
  epdp_ptyl ppf sc tys

and epdp_fun_univ_ex (sc : EcScope.scope) (ppf : Format.formatter) 
(ty1 : ty) (ty2 : ty) : unit =
  failure "epdp for function types not implemented"
(*TODO naming convention for function  epdps*)
(*---------------------------------------------------------------------------*)

let print_epdp_data_univ (sc : EcScope.scope) (ppf : Format.formatter) 
(params_map : ty_index IdMap.t) : unit =
  let tys = List.map (fun (_,ty) -> ty) (params_map_to_list params_map) in
  match tys with
  | [] -> Format.fprintf ppf "@ epdp_unit_univ"
  | [t] -> epdp_ty_univ_ex sc ppf t
  | _ -> epdp_tuple_univ_ex sc ppf tys

(*------------------------------------------------------------------------*)

let print_record_field_nl
(sc : EcScope.scope)
(ppf : Format.formatter)
(fn : string)
(ty : EcTypes.ty)
: unit =
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  Format.fprintf ppf "@[%s :@ @[%a@];@]" fn (EcPrinting.pp_type ppe) ty;
  print_newline ppf

let msg_ty_name (name : string) : string = "_"^name

let ty_dec (name : string) : string =
  "type "^(msg_ty_name name)^" ="

let print_ident_braces_nl (ppf : Format.formatter) =
  Format.fprintf ppf "@[<hov 2>{@.@[<hov 1>"

let print_braces_dedent_nl (ppf : Format.formatter) =
  Format.fprintf ppf "@]@.}@]"

let print_dir_message
(ppf : Format.formatter)
(sc : EcScope.scope)
(name : string)
(mb : message_body_tyd)
    : unit =
  let print_dir_message_record : unit =
    print_str_nl ppf (ty_dec name);
    print_ident_braces_nl ppf;
    print_record_field_nl sc ppf (name_record_func name) addr_ty;
    print_record_field_nl sc ppf (name_record_dir_port name mb) port_ty;
    print_str_nl ppf "(*data*)";
    List.iter (fun (s,t) ->
        print_record_field_nl sc ppf (name_record name s) t)
      (params_map_to_list mb.params_map);
    print_braces_dedent_nl ppf
  in
  let print_enc_op : unit = ()
    
  in
  print_dir_message_record

(*let write_message (ppf : Format.formatter) (sh : shadowed) 
  (tag : int) (name : string) (mb : message_body_tyd) : shadowed =
  write_type ppf (msg_type sh name mb);
  let sh, op = enc_op ppf sh tag name mb in
  write_operator ppf op;
  write_operator ppf (dec_op sh tag name mb);
  let epdpop = epdp_op name in
  write_operator ppf epdpop;
  let epdplem = lemma_epdp (ul epdpop.po_name) in
  write_lemma ppf epdplem;
  let lename = ul epdplem.pa_name in
  write_hint_simplify ppf lename;
  write_hint_rewrite ppf _epdp lename;
  write_lemma ppf (lemma_eq_of_valid sh tag name mb);
  sh*)

let gen_basic_dir
(sc : EcScope.scope)
(id : string)
(bibt : basic_inter_body_tyd)
: string =
  let sf = Format.get_str_formatter () in
  let name = uc_name id in
  print_str_nl sf (open_theory name);
  print_str_nl sf pi_op;
  let bibtl = IdMap.bindings bibt in
  List.iter (fun (n, mb) -> print_dir_message sf sc n mb) bibtl;
  print_str_nl sf (close_theory id);
  Format.flush_str_formatter ()

let gen_dir (sc : EcScope.scope) (id : string) (it : inter_tyd) : string = 
  let ibt = unloc it in
  match ibt with
  | BasicTyd bibt -> gen_basic_dir sc id bibt
  | CompositeTyd _ -> "" (*TODO*)
