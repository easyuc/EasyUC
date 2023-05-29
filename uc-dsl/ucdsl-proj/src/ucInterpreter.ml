(* UcInterpreter module *)

open EcSymbols
open EcFol

open UcMessage
open UcSpec
open UcTypedSpec
open UcSpecTypedSpecCommon
open UcTypecheck

(* the (positive) ints in a real_world, are the base adverserial port
   indices for the unit of the given functionality; these will also be
   the adversarial port indices for communication between the unit's
   ideal functionality and simulator *)

type real_world = symb_pair * int * real_world_arg list

and real_world_arg =
  | RWA_Real  of real_world
  | RWA_Ideal of symb_pair * int

(* the (positive) ints in an ideal_world are the port indices for
   communication between ideal functionalities and simulators *)

type ideal_world = {
  iw_ideal_func : symb_pair * int;
  iw_main_sim   : symb_pair * int;
  iw_other_sims : (symb_pair * int) list
}

type worlds = {
  worlds_real  : real_world;
  worlds_ideal : ideal_world
}

let pp_worlds (fmt : Format.formatter) (w : worlds) : unit =
  let pp_symb_pair_int (fmt : Format.formatter) (sp,i : symb_pair * int) 
  : unit =
    Format.fprintf fmt "@[%s.%s:%i@]" (fst sp) (snd sp) i
  in
  let rec pp_real_world_arg (fmt : Format.formatter) (rwa : real_world_arg) 
  : unit =
    match rwa with
    | RWA_Real rw -> Format.fprintf fmt "%a" pp_real_world rw
    | RWA_Ideal (sp,i) -> Format.fprintf fmt "%a" pp_symb_pair_int (sp,i)
  and pp_real_world_argl (fmt : Format.formatter) (rwal : real_world_arg list)
  : unit =
    match rwal with
    | [] -> Format.fprintf fmt ""
    | rwa::[] ->
      Format.fprintf fmt "%a" 
        pp_real_world_arg rwa
    | rwa::tl ->
      Format.fprintf fmt "%a, %a"
        pp_real_world_arg rwa 
        pp_real_world_argl tl
  and pp_real_world (fmt : Format.formatter) (rw : real_world) : unit =
    let sp,i,rwal = rw in
    match rwal with
    | [] ->
      Format.fprintf fmt "@[%a@]" 
        pp_symb_pair_int (sp,i) 
    | _ ->
      Format.fprintf fmt "@[%a(%a)@]" 
        pp_symb_pair_int (sp,i) 
        pp_real_world_argl rwal
  in
  let rec pp_simsl (fmt : Format.formatter) (spil : (symb_pair * int) list)
  : unit =
    match spil with
    | [] -> 
      Format.fprintf fmt ""
    | spi::tl -> 
      Format.fprintf fmt " * %a%a"
        pp_symb_pair_int spi
        pp_simsl tl
  in
  let pp_ideal_world (fmt : Format.formatter) (iw : ideal_world) : unit =
    Format.fprintf fmt "@[%a@ /@ %a%a@]"
      pp_symb_pair_int iw.iw_ideal_func
      pp_symb_pair_int iw.iw_main_sim
      pp_simsl iw.iw_other_sims
  in
  Format.fprintf fmt "@[%a@ ~@ %a@]@." 
    pp_real_world w.worlds_real 
    pp_ideal_world w.worlds_ideal

let pp_form (fmt : Format.formatter) (f : form) : unit =
  let env = UcEcInterface.env() in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pp_form = EcPrinting.pp_form ppe in
  pp_form fmt f

let pp_sent_msg_expr_tyd (fmt : Format.formatter) (sme : sent_msg_expr_tyd) 
      : unit =
  let pp_msg_dir (fmt : Format.formatter) (dir : msg_dir) : unit =
    let s = match dir with
      | In   -> "Incoming"
      | Out  -> "Outgoing"
    in
    Format.fprintf fmt "%s" s
  in
  let pp_msg_mode (fmt : Format.formatter) (mode : msg_mode) : unit =
    let s = match mode with
      | Dir -> "direct"
      | Adv -> "adversarial"
    in
    Format.fprintf fmt "%s message:" s
  in
  let pp_msg (fmt : Format.formatter) 
      (a : form * msg_path_u * form list * form) : unit =
    let inp,path,args,outp = a in
    let pp_portform (fmt : Format.formatter) (f : form) : unit =
      if (is_pvar f)||(is_local f)
      then Format.fprintf fmt "%a" pp_form f
      else Format.fprintf fmt "(%a)" pp_form f
    in
    let pp_mpath (fmt : Format.formatter) (path : msg_path_u) : unit =
      let rec pp_strl (fmt : Format.formatter) (strl : string list) : unit =
        match strl with
        | [] -> Format.fprintf fmt ""
        | s::[] -> Format.fprintf fmt "%s." s
        | s::tl -> Format.fprintf fmt "%s.%a" s pp_strl tl
      in
      Format.fprintf fmt "%a%s" pp_strl path.inter_id_path path.msg
    in
    let rec pp_forml (fmt : Format.formatter) (forml : form list) : unit =
      match forml with
      | [] -> Format.fprintf fmt ""
      | ex::[] -> Format.fprintf fmt "%a" pp_form ex
      | ex::tl -> Format.fprintf fmt "%a,%a" pp_form ex pp_forml tl
    in
    Format.fprintf fmt "%a%a(%a)%a"
    pp_portform inp
    pp_mpath path
    pp_forml args
    pp_portform outp
  in
  Format.fprintf fmt "@[%a %a@ %a@]@."
    pp_msg_dir sme.dir
    pp_msg_mode sme.mode
    pp_msg (sme.in_port_form, sme.path, sme.args, sme.out_port_form)

let fun_expr_tyd_to_worlds (maps : maps_tyd) (fet : fun_expr_tyd) : worlds =
  let rec fun_expr_to_worlds_base (fet : fun_expr_tyd) (base : int)
        : worlds * int =
    match fet with
    | FunExprTydReal ((root, fun_id), fets) ->
        (match unit_info_of_root maps root with
         | UI_Singleton _ -> failure "cannot happen"
         | UI_Triple ti   ->
             let rec iter
                 (rwas : real_world_arg list) (base : int)
                 (sims : (symb_pair * int) list) (fets : fun_expr_tyd list)
                   : real_world_arg list * int * (symb_pair * int) list =
               match fets with
               | []          -> (rwas, base, sims)
               | fet :: fets ->
                   match fet with
                   | FunExprTydReal _   ->
                       let (worlds, base) =
                         fun_expr_to_worlds_base fet base in
                       iter (rwas @ [RWA_Real worlds.worlds_real]) base
                       (worlds.worlds_ideal.iw_main_sim ::
                        worlds.worlds_ideal.iw_other_sims @ sims)
                       fets
                   | FunExprTydIdeal sp ->
                       iter (rwas @ [RWA_Ideal (sp, base)]) (base + 1)
                       sims fets in
             let base' = base + ti.ti_num_adv_pis in
             let (rwas, base', sims) = iter [] base' [] fets in
             ({worlds_real  = ((root, fun_id), base, rwas);
               worlds_ideal =
                 {iw_ideal_func = ((root, ti.ti_ideal), base);
                  iw_main_sim   = ((root, ti.ti_sim), base);
                  iw_other_sims = sims}},
              base'))
     | FunExprTydIdeal _                    ->
         failure "should not be called with ideal functionality expression" in
  let (wrlds, _) = fun_expr_to_worlds_base fet 1 in
  wrlds

let fun_expr_to_worlds
    (root : symbol) (maps : maps_tyd) (fe : fun_expr) : worlds =
  let fet = inter_check_real_fun_expr root maps fe in
  fun_expr_tyd_to_worlds maps fet
