open UcTypedSpec
open EcLocation

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
  print_str_nl ppf (ty_dec name);
  print_ident_braces_nl ppf;
  print_record_field_nl sc ppf (name_record_func name) addr_ty;
  print_record_field_nl sc ppf (name_record_dir_port name mb) port_ty;
  print_str_nl ppf "(*data*)";
  List.iter (fun (s,t) ->
      print_record_field_nl sc ppf (name_record name s) t)
    (params_map_to_list mb.params_map);
  print_braces_dedent_nl ppf
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
