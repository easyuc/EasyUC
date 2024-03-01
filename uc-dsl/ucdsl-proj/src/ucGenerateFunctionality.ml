open UcTypedSpec
open EcTypes
open UcGenerateCommon

let state_name (name : string) : string = "_State_"^name
let state_type_name = "_state"
let uc__if = "UC__IF"


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


let gen_ideal_fun (sc : EcScope.scope) (id : string) (ifbt : ideal_fun_body_tyd)
    : string = 
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>@,@,";
  Format.fprintf sf "@[%s@]@,@," (open_theory uc__if);
  Format.fprintf sf "@[%a@]@," (print_state_type sc) ifbt.states;
  Format.fprintf sf "@[%s@]@," (close_theory uc__if);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (id : string) (ft : fun_tyd) : string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc id ifbt
  | FunBodyRealTyd rfbt  -> ""
