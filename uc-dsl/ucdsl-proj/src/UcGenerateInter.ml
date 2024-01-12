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
(name : string)
(mb : message_body_tyd)
: unit = ()

let gen_basic_dir (id : string) (bibt : basic_inter_body_tyd) : string =
  let sf = Format.get_str_formatter () in
  let name = uc_name id in
  print_str_nl sf (open_theory name);
  print_str_nl sf pi_op;
  let bibtl = IdMap.bindings bibt in
  List.iter (fun (n, mb) -> print_message sf n mb) bibtl;
  print_str_nl sf (close_theory id);
  Format.flush_str_formatter ()

let gen_dir (id : string) (it : inter_tyd) : string = 
  let ibt = unloc it in
  match ibt with
  | BasicTyd bibt -> gen_basic_dir id bibt
  | CompositeTyd _ -> "" (*TODO*)
