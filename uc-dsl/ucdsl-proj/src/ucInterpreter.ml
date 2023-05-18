(* UcInterpreter module *)

open EcSymbols
open EcUtils
open EcTypes

open UcMessage
open UcSpec
open UcTypedSpec
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
  let pp_symb_pair_int (fmt : Format.formatter) (sp,i : symb_pair * int) : unit =
    Format.fprintf fmt "@[%s.%s:%i@]" (fst sp) (snd sp) i
  in
  let rec pp_real_world_arg (fmt : Format.formatter) (rwa : real_world_arg) : unit =
    match rwa with
    | RWA_Real rw -> Format.fprintf fmt "%a" pp_real_world rw
    | RWA_Ideal (sp,i) -> Format.fprintf fmt "%a" pp_symb_pair_int (sp,i)
  and pp_real_world_argl (fmt : Format.formatter) (rwal : real_world_arg list) : unit =
    match rwal with
    | [] -> Format.fprintf fmt ""
    | [rwa] ->
      Format.fprintf fmt "%a" 
        pp_real_world_arg rwa
    | rwa::tl when tl<>[] ->
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
  let rec pp_simsl (fmt : Format.formatter) (spil : (symb_pair * int) list) : unit =
    match spil with
    | [] -> 
      Format.fprintf fmt ""
    | spi::tl -> 
      Format.fprintf fmt " * %a%a"
        pp_symb_pair_int spi
        pp_simsl tl
  in
  let pp_ideal_world (fmt : Format.formatter) (iw : ideal_world) : unit =
    Format.fprintf fmt "@[%a / %a%a@]"
      pp_symb_pair_int iw.iw_ideal_func
      pp_symb_pair_int iw.iw_main_sim
      pp_simsl iw.iw_other_sims
  in
  Format.fprintf fmt "@[%a ~ %a@]" 
    pp_real_world w.worlds_real 
    pp_ideal_world w.worlds_ideal

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
