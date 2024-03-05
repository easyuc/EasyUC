open UcTypedSpec
open EcTypes
open UcGenerateCommon

let state_name (name : string) : string = "_State_"^name
let state_type_name = "_state"
let uc__if = "UC__IF"
let _self = "_self"
let _adv = "_adv"
let _st = "_st"
let _m = "_m"
let _r = "_r"
let msg_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "msg")) []


let print_state_type
      (sc : EcScope.scope)
      (ppf : Format.formatter)
      (states : state_tyd IdMap.t)
    : unit =
  let s2e (sname, sbod : string * state_tyd) : (string * ty list) =
    let stys = snd (List.split (sparams_map_to_list
    (EcLocation.unloc sbod).params)) in
    ((state_name sname), stys)
  in
  let ste = List.map s2e (IdMap.bindings states) in
  let print_stys ppf stys : unit =
    let sty1 = List.hd stys in
    Format.fprintf ppf "%a" (pp_type sc) sty1;
    List.iter (fun ty -> Format.fprintf ppf "@ &@ %a" (pp_type sc) ty
      ) (List.tl stys)
  in
  Format.fprintf ppf "@[type %s = [ @]@;<0 2>" state_type_name;
  Format.fprintf ppf "@[<v>";
  List.iter (fun (sname, stys) ->
      if List.is_empty stys
      then Format.fprintf ppf "@[| %s@]@;" sname
      else Format.fprintf ppf "@[| %s of %a@]@;" sname print_stys stys
    ) ste;
  Format.fprintf ppf "@]@\n";
  Format.fprintf ppf "].@;"

let print_state_match_branch
      (ppf : Format.formatter) (id , st : string * state_tyd) : unit =
  let spn = fst (List.split (sparams_map_to_list
                               (EcLocation.unloc st).params)) in
  let print_state_params_names ppf spn =
    List.iter (fun s -> Format.fprintf ppf "%s@ " s) spn
  in
  Format.fprintf ppf "@[| %s %a=> {@]@;<0 2>@[<v>"
    (state_name id) print_state_params_names spn;
  Format.fprintf ppf "@]@;}@;"

let print_ideal_module (sc : EcScope.scope) (ppf : Format.formatter)
      (id , ifbt : string * ideal_fun_body_tyd) : unit =
  Format.fprintf ppf "@[module %s = {@]@;<0 2>@[<v>" (uc_name id);
  Format.fprintf ppf "@[var %s, %s : %a@]@;" _self _adv (pp_type sc) addr_ty;
  Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name;
  Format.fprintf ppf "@[proc init(self_ adv_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
  Format.fprintf ppf "@[%s <- self_; %s <- adv_; %s <- %s;@]@;@[}@]@;"
    _self _adv _st (state_name (initial_state_id_of_states ifbt.states));
  Format.fprintf ppf "@[proc parties(%s : %a) : %a option = {@]@;<0 2>@[<v>"
    _m (pp_type sc) msg_ty (pp_type sc) msg_ty;
  Format.fprintf ppf "@[var %s : %a option <- None;@]@;" _r (pp_type sc) msg_ty;
  Format.fprintf ppf "@[match %s with@]@;" _st;
  IdMap.iter (fun id st -> Format.fprintf ppf "%a"
                             print_state_match_branch (id, st)) ifbt.states;
  Format.fprintf ppf "@[end;@]@;";
  Format.fprintf ppf "@[return %s;@]" _r;
  Format.fprintf ppf "@]@;}";
  Format.fprintf ppf "@]@;}.";
  ()
  

let gen_ideal_fun (sc : EcScope.scope) (id : string) (ifbt : ideal_fun_body_tyd)
    : string = 
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>@,@,";
  Format.fprintf sf "@[%s@]@,@," (open_theory uc__if);
  Format.fprintf sf "@[%a@]@," (print_state_type sc) ifbt.states;
  Format.fprintf sf "@[%a@]@," (print_ideal_module sc) (id, ifbt);
  Format.fprintf sf "@[%s@]@," (close_theory uc__if);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (id : string) (ft : fun_tyd) : string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc id ifbt
  | FunBodyRealTyd rfbt  -> ""
