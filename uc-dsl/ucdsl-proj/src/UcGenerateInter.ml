open UcTypedSpec
open EcLocation

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

let print_message
(ppf : Format.formatter)
(sc : EcScope.scope)
(name : string)
(mb : message_body_tyd)
: unit = ()
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
  List.iter (fun (n, mb) -> print_message sf sc n mb) bibtl;
  print_str_nl sf (close_theory id);
  Format.flush_str_formatter ()

let gen_dir (sc : EcScope.scope) (id : string) (it : inter_tyd) : string = 
  let ibt = unloc it in
  match ibt with
  | BasicTyd bibt -> gen_basic_dir sc id bibt
  | CompositeTyd _ -> "" (*TODO*)
