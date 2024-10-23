open UcTypedSpec
open EcTypes
open EcLocation
open UcMessage
open UcGenerateCommon

type tag =
  | TagNoInter       (* communication not involving messages of an
                        interface *)
  | TagComposite of  (* message is to/from composite interface *)
      string *       (* unit root file name *)
      string         (* message name *)
  | TagBasic     of  (* message is to/from basic interface *)
      string *       (* unit root file name *)
      string         (* message name *)

let print_tag (ppf : Format.formatter) (tag : tag) : unit =
  match tag with
  | TagNoInter -> Format.fprintf ppf "TagNoInter"
  | TagComposite (root, name) -> Format.fprintf ppf "TagComposite@ %s@ %s" root name
  | TagBasic (root, name) -> Format.fprintf ppf "TagBasic@ %s@ %s" root name

let print_epdp_tag_univ (ppf : Format.formatter) (sc : EcScope.scope) : unit =
  let env = EcScope.env sc in
  let qepdp = (["Top";"UCBasicTypes"], "epdp_tag_univ") in
  let pth, oper = EcEnv.Op.lookup qepdp env in
  let epdp_opex = e_op pth [] oper.op_ty in
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  Format.fprintf ppf "@[%a@]" (EcPrinting.pp_expr ppe) epdp_opex

(* iff ucdsl message declaration has some port, it is a direct message *)
let isdirect (mb : message_body_tyd) : bool =
  match mb.port with
  | None -> false
  | Some _ -> true

let __adv_if_pi = "_adv_if_pi"

let abs_oper_int (name : string) : string = "op "^name^" : int."

let pi_op : string = abs_oper_int _pi

let print_newline (ppf : Format.formatter) : unit =
  Format.fprintf ppf "@;"

let print_str_nl (ppf : Format.formatter) (str : string) : unit =
  Format.fprintf ppf "%s@;" str;
  print_newline ppf

let name_epdp_op (tyname : string) : string = "epdp_"^tyname^"_univ"

let epdp_enc_field : string = "enc"

let enc_op_name (name : string) : string = "enc_"^name


(* print epdp for message data ----------------------------------------------*)

(* epdp for constructed types -----------------------------------------------*)

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
              | None -> if qtp = (["Top"; "UCUniv"], "univ")
                        then EcEnv.Op.lookup
                               (["Top"; "UCEncoding"], "epdp_id") env
                        else failure
                          ("couldn't find epdp operator for "^
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
     let qbase = (["Top";"UCUniv"], name) in
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

let print_enc_data (sc : EcScope.scope) 
(var_name : string)
(msg_name : string)
(ppf : Format.formatter)
(params_map : ty_index IdMap.t) 
: unit =
  let print_enc_args (var_name : string) (msg_name : string )
  (ppf : Format.formatter) (params_map : ty_index IdMap.t) : unit =
    let pns = fst (List.split (params_map_to_list params_map)) in
    match pns with
    | [] -> Format.fprintf ppf "@[()@]"
    | [pn] -> Format.fprintf ppf "@[%s.`%s@]" var_name (name_record msg_name pn)
    | pn::tl ->
       let print_tl_args (ppf : Format.formatter) (pns : string list) =
         List.iter (fun pn -> Format.fprintf ppf "@[,@ %s.`%s@]"
                                var_name (name_record msg_name pn)) tl
         in
       Format.fprintf ppf "@[(%s.`%s%a)@]"
         var_name (name_record msg_name pn) print_tl_args tl
  in
  Format.fprintf ppf "@[@ (%a).`%s@ %a@]"
    (print_epdp_data_univ sc) params_map
    epdp_enc_field
    (print_enc_args var_name msg_name) params_map

(*------------------------------------------------------------------------*)

let print_record_field_nl
(sc : EcScope.scope)
(ppf : Format.formatter)
(fn : string)
(ty : EcTypes.ty)
: unit =
  Format.fprintf ppf "@,@[%s :@ %a;@]" fn (pp_type sc) ty

let dec_op_name (name : string) : string = "dec_"^name

let tag_op_name (name : string) : string = "_tag_"^name

let ty_dec (name : string) : string =
  "type "^(msg_ty_name name)^" ="

let print_ident_braces_nl (ppf : Format.formatter) =
  Format.fprintf ppf "{@[<v 1>"

let print_braces_dedent_nl (ppf : Format.formatter) =
  Format.fprintf ppf "@]@,}@,"

let print_str_as_ec_str (ppf : Format.formatter) (s : string) : unit =
  let intarr = List.init (String.length s)
                 (fun i -> Char.code (s.[i])) in
  Format.fprintf ppf "@[[";
  if intarr<>[]
  then begin
    Format.fprintf ppf "%i" (List.hd intarr);
    List.iter (fun i ->
      Format.fprintf ppf ";@ %i" i) (List.tl intarr)
  end;
  Format.fprintf ppf "].@]"

let print__name_as_ec_str_op (ppf : Format.formatter)
(n : string) : unit =
  Format.fprintf ppf "@[op@ _%s@ =@  %a@ (*%s@ as@ ascii@ array*)@]@,@,"
    n print_str_as_ec_str n n

let get_root_from_tag (tag : tag) : string =
  match tag with
  | TagComposite (r,_) -> r 
  | TagBasic (r,_) -> r
  | TagNoInter -> failure "TagNoInter has no root"

let print_message
(ppf : Format.formatter)
(sc : EcScope.scope)
(tag : tag)
(mty_name : string)
(mb : message_body_tyd)
    : unit =

  let _mty_name = msg_ty_name mty_name in
  let _enc_op_name = enc_op_name _mty_name in
  let _dec_op_name = dec_op_name _mty_name in
  let _epdp_op_name = epdp_op_name _mty_name in
  let _tag_op_name = tag_op_name _mty_name in
  let isdirect = isdirect mb in
  
  let print_message_record () : unit =
    Format.fprintf ppf "@[%s@]@," (ty_dec mty_name);
    Format.fprintf ppf "{@[<v 1>";
    print_record_field_nl sc ppf (name_record_func mty_name) addr_ty;
    if isdirect
    then print_record_field_nl sc ppf
           (name_record_dir_port mty_name mb) port_ty
    else print_record_field_nl sc ppf
           (name_record_adv mty_name) addr_ty
    ;
    Format.fprintf ppf "@,@[(*data*)@]";
    List.iter (fun (s,t) ->
        print_record_field_nl sc ppf (name_record mty_name s) t)
      (params_map_to_list mb.params_map);
    Format.fprintf ppf "@]@,}.@,"
  in

  let print_tag_mty_name_op () : unit =
    let t,r,m = match tag with
    | TagComposite (r,m) -> ("TagComposite", r, m) 
    | TagBasic (r,m) -> ("TagBasic",r,m)
    | TagNoInter -> failure "TagNoInter should not show up here"
    in
    print__name_as_ec_str_op ppf m;
    Format.fprintf ppf "@[op@ %s@ =@  %s@ _%s@ _%s.@]@,"
      _tag_op_name t r m
  in

  let print_enc_op_body (ppf : Format.formatter) (mb : message_body_tyd) : unit =
    let var_name = "x" in
    let print_otherport ppf : unit =
      if isdirect
      then Format.fprintf ppf "@[%s.`%s@]"
             var_name (name_record_dir_port mty_name mb)
      else Format.fprintf ppf "@[(%s.`%s,@ %s)@]"
             var_name (name_record_adv mty_name) __adv_if_pi
    in
    let print_selfport ppf () : unit = Format.fprintf ppf "@[%s.`%s@]"
      var_name (name_record_func mty_name)
    in
    let print_ptsource ppf dir =
      if dir = UcSpecTypedSpecCommon.In
      then print_otherport ppf
      else Format.fprintf ppf "(%a,@ %s)" print_selfport () _pi
    in
    let print_ptdest ppf dir =
      if dir = UcSpecTypedSpecCommon.In
      then Format.fprintf ppf "(%a,@ %s)" print_selfport () _pi
      else print_otherport ppf
    in
    let mode = if isdirect then mode_Dir else mode_Adv in
      
    Format.fprintf ppf "@[(%s,@ %a,@ %a,@ %s,@ %a)@]"
      mode
      print_ptdest mb.dir
      print_ptsource mb.dir
      _tag_op_name
      (print_enc_data sc var_name mty_name) mb.params_map
  in

  let print_enc_op () : unit = 
    let var_name = "x" in
    Format.fprintf ppf "@[op@ %s@ (%s@ :@ %s)@ :@ msg@ =@;@[<v 2>%a@]@]@,.@,"
      _enc_op_name var_name _mty_name
      print_enc_op_body mb   
  in

  let print_dec_op () : unit =
    let print_dec_op_body (ppf : Format.formatter) (mb : message_body_tyd): unit =
      let otherport = if mb.dir = In then "pt2" else "pt1" in
      let otherportoraddr = if isdirect then otherport else otherport ^".`1" in
      let selfport = if mb.dir = In then "pt1" else "pt2" in
      let print_params_vars ppf pm : unit =
        let pns = fst (List.split (params_map_to_list pm)) in
        if pns<>[]
        then begin
          Format.fprintf ppf "%s" (name_record mty_name (List.hd pns));
          List.iter (fun pn -> Format.fprintf ppf "@ ,%s"
                               (name_record mty_name pn)) (List.tl pns)
        end
        
      in
      let print_data_assign ppf pm : unit =
        let pns = fst (List.split (params_map_to_list pm)) in
        List.iter (fun pn -> let n = (name_record mty_name pn) in
            Format.fprintf ppf "@,@[%s@ =@ %s;@]" n n)  pns
      in
      let not_mode = if isdirect then mode_Adv else mode_Dir in
      let otherfield = if isdirect
                       then (name_record_dir_port mty_name mb)
                       else (name_record_adv mty_name) in
      let adv_pi_not = if isdirect
                       then ""
                       else otherport^".`2 <> "^__adv_if_pi^" \\/ " in
      Format.fprintf ppf
      "@[let@ (mod,@ pt1,@ pt2,@ tag,@ v)@ =@ m@]@,";
      Format.fprintf ppf 
      "@[in@ (mod@ =@ %s@ \\/@ %s%s.`2@ <>@ pi@ \\/@ tag@ <>@ %s)@ ?@]"
      not_mode adv_pi_not selfport _tag_op_name;
      Format.fprintf ppf "@,@[<v 2>  ";
      Format.fprintf ppf "@[None@ :@]@,";
      Format.fprintf ppf "@[match@ (%a).`dec@ v@ with@]@,"
        (print_epdp_data_univ sc) mb.params_map;
      Format.fprintf ppf "@[| None   => None@]@,";
      Format.fprintf ppf "@[| Some p =>@]";
      Format.fprintf ppf "@,@[<v 2>  ";
      if not (IdMap.is_empty mb.params_map) then
      if (IdMap.cardinal mb.params_map) > 1 then
        Format.fprintf ppf "@[let@ (%a)@ =@ p@ in@]@,"
          (print_params_vars) mb.params_map
      else
        Format.fprintf ppf "@[let@ %a@ =@ p@ in@]@,"
          (print_params_vars) mb.params_map
      ;
      Format.fprintf ppf "@[Some@]";
      Format.fprintf ppf "@,@[<v 2>{|@,";
      Format.fprintf ppf "@[%s = %s.`1;@ %s@ =@ %s;@]"
        (name_record_func mty_name)
        selfport
        otherfield
        otherportoraddr;
      Format.fprintf ppf "%a"
        (print_data_assign) mb.params_map;
      Format.fprintf ppf "@]@,|}";
      Format.fprintf ppf "@]@,end";
      Format.fprintf ppf "@]"
    in
    let var_name="m" in
    Format.fprintf ppf
      "@[op@ [opaque smt_opaque]@ %s@ (%s@ :@ msg)@ :@ %s@ option =@,@[<v 2>  %a@]@,.@]@,@,"
      _dec_op_name var_name _mty_name
      print_dec_op_body mb 
  in

  let print_epdp_op () : unit =
    Format.fprintf ppf "@[op@ %s@ =@ @[{|enc@ =@ %s; dec = %s|}@].@]@,@,"
    _epdp_op_name _enc_op_name _dec_op_name
  in

  let print_valid_epdp_lemma () : unit =
    let pt2 = if isdirect then "pt2" else "[pt2_1 pt2_2]" in
    let ptsource =
      if mb.dir = UcSpecTypedSpecCommon.In
      then pt2
      else "[pt1_1 pt1_2]"
    in
    let ptdest =
      if mb.dir = UcSpecTypedSpecCommon.In
      then "[pt1_1 pt1_2]"
      else pt2
    in
    let print_data_get ppf pm : unit =
      let nr pn = (name_record mty_name pn) in
      let pns = fst (List.split (params_map_to_list pm)) in
      if pns<>[]
      then
        begin
          Format.fprintf ppf "@[<h>u.`%s@]" (nr (List.hd pns));
          List.iter (fun pn ->
            Format.fprintf ppf "@ ,@[<h>u.`%s@]" (nr pn))  (List.tl pns)
        end
      else ()
    in
    Format.fprintf ppf "lemma valid_%s : valid_epdp %s.@,"
    _epdp_op_name _epdp_op_name;
    Format.fprintf ppf "proof.@,";
    Format.fprintf ppf "apply epdp_intro.@,";
    Format.fprintf ppf "move => x.@,";
    Format.fprintf ppf "rewrite /%s /= /%s /%s /= !epdp /=.@,"
    _epdp_op_name _dec_op_name _enc_op_name;
    Format.fprintf ppf "by case x.@,";
    Format.fprintf ppf "move => [mod %s %s tag v] u.@,"
    ptdest ptsource;
    Format.fprintf ppf "rewrite /%s /%s /%s /=.@,"
      _epdp_op_name _dec_op_name _enc_op_name;
    if isdirect
    then Format.fprintf ppf
           "case (mod = Adv \\/ pt1_2 <> %s \\/ tag <> %s) => //.@,"
         _pi _tag_op_name
    else Format.fprintf ppf
    "case (mod = Dir \\/ pt2_2 <> %s \\/ pt1_2 <> %s \\/ tag <> %s) => //.@,"
         __adv_if_pi _pi  _tag_op_name;
      Format.fprintf ppf "rewrite !negb_or /= %s.@,"
    (if isdirect then "not_adv" else "not_dir");
    Format.fprintf ppf "move => [#] -> %s-> -> match_eq_some /=.@,"
    (if isdirect then "" else "-> ");
    Format.fprintf ppf "have val_v :@,";
    Format.fprintf ppf "  (%a).`dec v =@,"
    (print_epdp_data_univ sc) mb.params_map;
    Format.fprintf ppf "@[  Some (%a).@]@,"
    print_data_get mb.params_map;
    Format.fprintf ppf "  move : match_eq_some.@,";
    Format.fprintf ppf "  case ((%a).`dec v) => //.@,"
      (print_epdp_data_univ sc) mb.params_map;
    if (IdMap.cardinal mb.params_map)>1 then
      Format.fprintf ppf "  by case.@,";
    Format.fprintf ppf "move : match_eq_some.@,";
    Format.fprintf ppf "rewrite val_v /= => <- /=.@,";
    Format.fprintf ppf "apply epdp_dec_enc => //.@,";
    Format.fprintf ppf "qed.@,@,"
  in

  let print_epdp_hints () : unit =
    Format.fprintf ppf "hint simplify [eqtrue] valid_%s.@,"
    _epdp_op_name;
    Format.fprintf ppf "hint rewrite epdp : valid_%s.@,@,"
    _epdp_op_name;
  in
  
  let print_eq_of_valid_lemma () : unit =
    let print_xi_data_many_times ppf i : unit =
      for i = 1+2 to i+2 do
        Format.fprintf ppf "@ x%i" i;
      done  
    in
    Format.fprintf ppf "lemma eq_of_valid_%s (m : msg) :@,"
    _mty_name;
    Format.fprintf ppf "  is_valid %s m =>@,"
    _epdp_op_name;
    Format.fprintf ppf "  m =@,";
    Format.fprintf ppf "  let x = oget (%s.`dec m) in@,"
    _epdp_op_name;
    Format.fprintf ppf "@[<v 4>%a@].@,"
    print_enc_op_body mb;
    Format.fprintf ppf "proof.@,";
    Format.fprintf ppf "rewrite /is_valid.@,";
    Format.fprintf ppf "move => val_m.@,";
    Format.fprintf ppf "have [] x : exists (x : %s), %s.`dec m = Some x.@,"
    _mty_name _epdp_op_name;
    Format.fprintf ppf "  exists (oget (%s m)); by rewrite -some_oget.@,"
    _dec_op_name;
    Format.fprintf ppf "@[case x => x1 x2%a.@]@,"
    print_xi_data_many_times (IdMap.cardinal mb.params_map);
    Format.fprintf ppf "move => /(epdp_dec_enc _ _ _ valid_%s) <-.@,"
    _epdp_op_name;
    Format.fprintf ppf "by rewrite !epdp.@,";
    Format.fprintf ppf "qed.@,@,";
  in
  
  print_message_record ();
  print_tag_mty_name_op();
  print_enc_op ();
  print_dec_op ();
  print_epdp_op ();
  print_valid_epdp_lemma ();
  print_epdp_hints ();
  print_eq_of_valid_lemma ()

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

let gen_basic_int
(sc : EcScope.scope)
(id : string)
(root : string)
(bibt : basic_inter_body_tyd)
: string =
  let sf = Format.get_str_formatter () in
  let name = bi_name id in
  Format.fprintf sf "@[<v>";
  print_str_nl sf (open_abstract_theory name);
  print_str_nl sf pi_op;
  print__name_as_ec_str_op sf root;
  let bibtl = IdMap.bindings bibt in
  List.iter (fun (n, mb) ->
      let tag = (TagBasic (root, n)) in
      print_message sf sc tag n mb) bibtl;
  print_str_nl sf (close_theory name);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_comp_int (id : string) (sm : string IdMap.t) : string =
  let sf = Format.get_str_formatter () in
  let name = uc_name id in
  Format.fprintf sf "@[<v>";
  print_str_nl sf (open_theory name);
  let sml = IdMap.bindings sm in
  List.iteri (fun i (name, basicname) ->
    Format.fprintf sf "@[clone %s as %s with@]@,"
      (bi_name basicname) name;
    Format.fprintf sf "@[  op %s = %i@]@,"
      _pi (i+1);
    Format.fprintf sf "@[proof *.@]@,@,"          
    ) sml;
  print_str_nl sf (close_theory name);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_int (sc : EcScope.scope)
(root : string ) (id : string) (it : inter_tyd) : string = 
  let ibt = unloc it in
  match ibt with
  | BasicTyd bibt -> gen_basic_int sc id root bibt
  | CompositeTyd sm -> gen_comp_int id sm
