(* UcInterpreter module *)

open Format

open EcSymbols
open EcLocation
open EcUtils
open EcTypes
open EcFol
open EcEnv

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
      Format.fprintf fmt "%a,@ %a"
        pp_real_world_arg rwa 
        pp_real_world_argl tl
  and pp_real_world (fmt : Format.formatter) (rw : real_world) : unit =
    let sp,i,rwal = rw in
    match rwal with
    | [] ->
      Format.fprintf fmt "@[%a@]" 
        pp_symb_pair_int (sp,i) 
    | _ ->
      Format.fprintf fmt "@[<hv>%a@,(@[%a@])@]" 
        pp_symb_pair_int (sp,i) 
        pp_real_world_argl rwal
  in
  let rec pp_simsl (fmt : Format.formatter) (spil : (symb_pair * int) list)
  : unit =
    match spil with
    | [] -> 
      Format.fprintf fmt ""
    | [spi] ->
      Format.fprintf fmt " *@ %a"
        pp_symb_pair_int spi
    | spi::tl -> 
      Format.fprintf fmt " *@ %a%a"
        pp_symb_pair_int spi
        pp_simsl tl
  in
  let pp_ideal_world (fmt : Format.formatter) (iw : ideal_world) : unit =
    Format.fprintf fmt "@[<hv>%a /@ @[%a%a@]@]"
      pp_symb_pair_int iw.iw_ideal_func
      pp_symb_pair_int iw.iw_main_sim
      pp_simsl iw.iw_other_sims
  in
  Format.fprintf fmt "@[%a ~@ %a@]@." 
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
      if is_local f
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
      | ex::[] -> Format.fprintf fmt "@[%a@]" pp_form ex
      | ex::tl -> Format.fprintf fmt "@[%a@]@,,%a" pp_form ex pp_forml tl
    in
    Format.fprintf fmt "@[%a@,@[<hv>%a@]@,(@[<hv>%a@])@,%a@]"
    pp_portform inp
    pp_mpath path
    pp_forml args
    pp_portform outp
  in
  Format.fprintf fmt "@[<hv>%a %a@ %a@]@."
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

(* like UcTypedSpec.instruction_tyd and UcTypedSpec.instruction_tyd_u,
   but includes Pop instruction for popping a frame of local context *)

type instr_interp_u =
  | Assign of lhs * expr
  | Sample of lhs * expr
  | ITE of expr * instr_interp list located *
           instr_interp list located option
  | Match of expr * match_clause_interp list located
  | SendAndTransition of send_and_transition_tyd
  | Fail
  | Pop  (* pop frame of local context *)

and instr_interp = instr_interp_u located

and match_clause_interp = symbol * (bindings * instr_interp list located)

let rec create_instr_interp (it : instruction_tyd) : instr_interp =
  mk_loc (loc it) (create_instr_interp_u (unloc it))

and create_instr_interp_list_loc (its : instruction_tyd list located)
      : instr_interp list located =
  mk_loc (loc its) (List.map create_instr_interp (unloc its))

and create_instr_interp_u (itu : instruction_tyd_u) : instr_interp_u =
  match itu with
  | UcTypedSpec.Assign (lhs, exp)     -> Assign (lhs, exp)
  | UcTypedSpec.Sample (lhs, exp)     -> Sample (lhs, exp)
  | UcTypedSpec.ITE (exp, tins, eins) ->
      ITE
      (exp,
       create_instr_interp_list_loc tins,
       omap create_instr_interp_list_loc eins)
  | UcTypedSpec.Match (exp, clauses)  ->
      Match
      (exp,
       mk_loc (loc clauses)
       (List.map create_match_clause_interp (unloc clauses)))
  | UcTypedSpec.SendAndTransition sat -> SendAndTransition sat
  | UcTypedSpec.Fail                  -> Fail

and create_match_clause_interp ((sym, (bndgs, ins)) : match_clause_tyd)
      : match_clause_interp =
  (sym, (bndgs, create_instr_interp_list_loc ins))

(* a local context is a nonempty stack of maps from identifers (local
   variables or bound identifiers (state parameters or ones bound by
   message match clauses or ordinary match clauses)) to formulas,
   which should be well typed in the global context

   the head of the list is the bottom of the stack, ..., and the last
   element of the list is the top of the stack *)

type local_context = form EcIdent.Mid.t list

type local_context_base =
  | LCB_Var     of EcIdent.t * ty
  | LCB_EnvPort of form * form  (* both of type address *)
  | LCB_IntPort of EcIdent.t * form  (* of type port *)

let lc_create (lcbs : local_context_base list) : local_context =
  [EcIdent.Mid.of_list
   (List.map
    (fun lcb ->
       match lcb with
       | LCB_Var (id, ty)                  ->
           (id, f_op EcCoreLib.CI_Witness.p_witness [] ty)
       | LCB_EnvPort (func_form, adv_form) ->
           (envport_id,
            f_app (form_of_expr mhr envport_op)
            [func_form; adv_form] (tfun port_ty tbool))
       | LCB_IntPort (id, port_form)       -> (id, port_form))
    lcbs)]

let pp_lc (env : env) (ppf : formatter) (lc : local_context) : unit =
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pp_frame_entry (ppf : formatter) ((id, form) : EcIdent.t * form)
        : unit =
    fprintf ppf "@[%a :@ %a@]"
    EcIdent.pp_ident id
    (EcPrinting.pp_form ppe) form in
  let pp_frame (ppf : formatter) (frame : form EcIdent.Mid.t) : unit =
    EcPrinting.pp_list "@, " pp_frame_entry ppf
    (EcIdent.Mid.bindings frame) in
  let rec pp_frames (ppf : formatter) (frames : form EcIdent.Mid.t list)
        : unit =
    match frames with
    | []              -> failure "cannot happen"
    | [frame]         -> pp_frame ppf frame
    | frame :: frames ->
        fprintf ppf "%a@;%a" pp_frame frame pp_frames frames in
  fprintf ppf "@[<v>%a@]" pp_frames lc

let lc_update_var (lc : local_context) (id : EcIdent.t) (f : form)
      : local_context =
  EcIdent.Mid.change (fun _ -> Some f) id (List.hd lc) :: List.tl lc

let lc_apply (lc : local_context) (e : expr) : form =
  let f = form_of_expr mhr e in
  let map =
    List.fold_left
    (fun acc nxt ->
       EcIdent.Mid.union (fun _ _ f -> Some f) acc nxt)
    (List.hd lc) (List.tl lc) in
  let subst =
    List.fold_left
    (fun acc (x, f) -> Fsubst.f_bind_local acc x f)
    Fsubst.f_subst_id (EcIdent.Mid.bindings map) in
  Fsubst.f_subst subst f

(* a global context is an EcEnv.LDecl.hyps *)

type global_context = LDecl.hyps

exception GCerror

let func_id         : EcIdent.t = EcIdent.create "func"
let adv_id          : EcIdent.t = EcIdent.create "adv"
let inc_func_adv_id : EcIdent.t = EcIdent.create "IncFuncAdv"

let gc_create (env : env) : global_context =
  let locs =
    [
      (func_id, EcBaseLogic.LD_var (addr_ty, None));
      (adv_id,  EcBaseLogic.LD_var (addr_ty, None));
      (inc_func_adv_id,
       EcBaseLogic.LD_hyp
       (form_of_expr mhr
        (e_app inc_op [e_local func_id addr_ty; e_local adv_id addr_ty]
         tbool)))
    ] in
  LDecl.init env ~locals:(List.rev locs) []

let env_of_gc (gc : global_context) : env = LDecl.toenv gc

(* pretty printer for global contexts: separates elements
   by commas, allowing breaks *)

let pp_gc (ppf : formatter) (gc : global_context) : unit =
  let ppe = EcPrinting.PPEnv.ofenv (env_of_gc gc) in
  let pp_loc ppe (ppf : formatter) (id, lk) : unit =
    match lk with
    | EcBaseLogic.LD_var (ty, _) ->
        fprintf ppf "@[%a :@ %a@]"
        EcIdent.pp_ident id
        (EcPrinting.pp_type ppe) ty
    | EcBaseLogic.LD_hyp form    ->
        fprintf ppf "@[%a :@ %a@]"
        EcIdent.pp_ident id
        (EcPrinting.pp_form ppe) form
    | _                          -> failure "cannot happen" in
  let locs = List.rev (LDecl.tohyps gc).h_local in
  EcPrinting.pp_list "@, " (pp_loc ppe) ppf locs

let gc_add_var (gc : global_context) (q : symbol) (ty : ty) : global_context =
  if LDecl.var_exists q gc
  then raise GCerror
  else LDecl.add_local (EcIdent.create q) (EcBaseLogic.LD_var (ty, None)) gc

let gc_add_hyp (gc : global_context) (q : symbol) (expr : expr)
      : global_context =
  if LDecl.hyp_exists q gc
  then raise GCerror
  else LDecl.add_local (EcIdent.create q)
       (EcBaseLogic.LD_hyp (form_of_expr mhr expr)) gc
