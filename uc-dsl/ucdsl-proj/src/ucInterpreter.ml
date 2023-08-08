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
open UcSpecTypedSpecCommon
open UcTypedSpec
open UcTypecheck

(* the values of type int in a real world are positive numbers with
   different interpretations depending upon whether the functionality
   is real or ideal

   with a real functionality, it is the base adversarial port index of
   the functionality's unit, which will be the port index of the
   adversary that the ideal functionality of the unit uses to
   communicate with its simulator (note that this ideal functionality
   will be implicit - an argument of the application of the real
   functionality simulated by the simulator)

   with an ideal functionality, it is the adversarial port index
   by which it communicates with the adversary (it will have no
   corresponding simulator) *)

type real_world = symb_pair * int * real_world_arg list

and real_world_arg =
  | RWA_Real  of real_world       (* a real functionality *)
  | RWA_Ideal of symb_pair * int  (* an ideal functionality *)

let adv_pi_of_rwa (rwa : real_world_arg) : int =
  match rwa with
  | RWA_Real (_, i, _) -> i
  | RWA_Ideal (_, i)   -> i

(* the ideal functionality is tagged with the adversarial port index
   of its simulator (the main one) - the second component of the data
   associated with the main simulator

   the second components of the data of the other simulators are their
   adversarial port indices - but their corresponding ideal
   functionalities will be implicit

   the third component of the data associated with a simulator
   consists of the adversarial port indices used by ideal
   functionalities that are arguments to the application of the real
   functionality that the simulator is simulating (used by an ideal
   functionality to either communicate with its simulator or with the
   adversary); the are listed in the order of the parameters of the
   real functionality *)

type ideal_world = {
  iw_ideal_func : symb_pair * int;
  iw_main_sim   : symb_pair * int * int list;
  iw_other_sims : (symb_pair * int * int list) list
}

type worlds = {
  worlds_real  : real_world;
  worlds_ideal : ideal_world
}

let pp_worlds (fmt : Format.formatter) (w : worlds) : unit =
  let pp_int (fmt : Format.formatter) (i : int) : unit =
    fprintf fmt "%d" i in
  let pp_paren_int_list (fmt : Format.formatter) (is : int list) : unit =
    if List.is_empty is
    then ()
    else Format.fprintf fmt "(@[%a@])"
         (EcPrinting.pp_list ",@, " pp_int) is in
  let pp_symb_pair_int (fmt : Format.formatter) (sp, i : symb_pair * int)
        : unit =
    Format.fprintf fmt "@[%s.%s:%i@]" (fst sp) (snd sp) i in
  let pp_symb_pair_int_int_list
      (fmt : Format.formatter) (sp, i, is : symb_pair * int * int list)
        : unit =
    Format.fprintf fmt "@[%s.%s:%i@,%a@]" (fst sp) (snd sp) i
    pp_paren_int_list is in

  let rec pp_real_world_arg (fmt : Format.formatter) (rwa : real_world_arg)
            : unit =
    match rwa with
    | RWA_Real rw      -> Format.fprintf fmt "%a" pp_real_world rw
    | RWA_Ideal (sp,i) -> Format.fprintf fmt "%a" pp_symb_pair_int (sp, i)
  and pp_real_world_argl (fmt : Format.formatter) (rwal : real_world_arg list)
        : unit =
    match rwal with
    | []        -> Format.fprintf fmt ""
    | rwa :: [] ->
      Format.fprintf fmt "%a"
        pp_real_world_arg rwa
    | rwa :: tl ->
      Format.fprintf fmt "%a,@ %a"
        pp_real_world_arg rwa
        pp_real_world_argl tl
  and pp_real_world (fmt : Format.formatter) (rw : real_world) : unit =
    let sp, i, rwal = rw in
    match rwal with
    | [] ->
      Format.fprintf fmt "@[%a@]"
        pp_symb_pair_int (sp, i)
    | _  ->
      Format.fprintf fmt "@[<hv>%a@,(@[%a@])@]"
        pp_symb_pair_int (sp, i)
        pp_real_world_argl rwal in

  let rec pp_simsl (fmt : Format.formatter)
          (spil : (symb_pair * int * int list) list) : unit =
    match spil with
    | []        ->
      Format.fprintf fmt ""
    | [spi]     ->
      Format.fprintf fmt " *@ %a"
        pp_symb_pair_int_int_list spi
    | spi :: tl ->
      Format.fprintf fmt " *@ %a%a"
        pp_symb_pair_int_int_list spi
        pp_simsl tl in

  let pp_ideal_world (fmt : Format.formatter) (iw : ideal_world) : unit =
    Format.fprintf fmt "@[<hv>%a /@ @[%a%a@]@]"
      pp_symb_pair_int iw.iw_ideal_func
      pp_symb_pair_int_int_list iw.iw_main_sim
      pp_simsl iw.iw_other_sims in
  Format.fprintf fmt "@[%a ~@ %a@]@."
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
                 (sims : (symb_pair * int * int list) list)
                 (fets : fun_expr_tyd list)
                   : real_world_arg list * int *
                     (symb_pair * int * int list) list =
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
                  iw_main_sim   =
                    ((root, ti.ti_sim), base,
                      List.map adv_pi_of_rwa rwas);
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

let func_id         : EcIdent.t = EcIdent.create "func"
let adv_id          : EcIdent.t = EcIdent.create "adv"
let inc_func_adv_id : EcIdent.t = EcIdent.create "IncFuncAdv"

let func_form : form = f_local func_id addr_ty
let adv_form  : form = f_local adv_id addr_ty

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

let gc_add_var (gc : global_context) (id : psymbol) (pty : pty)
      : global_context =
  let l = loc id in
  let id = unloc id in
  if LDecl.var_exists id gc
  then error_message l
       (fun ppf ->
          fprintf ppf
          ("@[identifier@ is@ already@ bound@ in@ global@ " ^^
           "context:@ %s@]")
          id)
  else try
         let env = LDecl.toenv gc in
         let ue = EcUnify.UniEnv.create None in
         let ty =
           UcTransTypesExprs.transty UcTransTypesExprs.tp_nothing env ue pty in
         LDecl.add_local (EcIdent.create id)
         (EcBaseLogic.LD_var (ty, None)) gc
       with
       | UcTransTypesExprs.TyError (l, env, tyerr) ->
           error_message l
           (fun ppf -> UcTypesExprsErrorMessages.pp_tyerror env ppf tyerr)

let gc_add_hyp (gc : global_context) (id : psymbol) (pexpr : pexpr)
      : global_context =
  let l = loc id in
  let id = unloc id in
  if LDecl.hyp_exists id gc
  then error_message l
       (fun ppf ->
          fprintf ppf
          ("@[@identifier@ is@ already@ bound@ in@ global@ " ^^
           "context:@ %s@]")
          id)
  else try
         let env = LDecl.toenv gc in
         let ue = EcUnify.UniEnv.create None in
         let (exp, _) = UcTransTypesExprs.transexp env ue pexpr in
         LDecl.add_local (EcIdent.create id)
         (EcBaseLogic.LD_hyp (form_of_expr mhr exp)) gc
       with
       | UcTransTypesExprs.TyError (l, env, tyerr) ->
           error_message l
           (fun ppf -> UcTypesExprsErrorMessages.pp_tyerror env ppf tyerr)

(* prover infos *)

type prover_infos = EcProvers.prover_infos

let update_prover_infos (env : EcEnv.env) (pi : prover_infos)
    (ppi : EcParsetree.pprover_infos) : prover_infos =
  try EcScope.Prover.pprover_infos_to_prover_infos env pi ppi with
  | EcScope.HiScopeError (lopt, s) ->
      opt_loc_error_message lopt
      (fun ppf -> fprintf ppf "prover infos error: %s" s)

(* configurations *)

type state = {  (* of ideal functionality, party or simulator *)
  id   : symbol;    (* name of state *)
  args : form list  (* arguments of state *)
}

let state_no_args (id : symbol) = {id = id; args = []}

type real_state = state IdMap.t  (* map from party names to their states *)

type ideal_state = state

type fun_state =
  | RealState  of real_state
  | IdealState of ideal_state

module IL =  (* domain: int list *)
  struct
    type t = int list
    let compare = Stdlib.compare
  end

module ILMap = Map.Make(IL)

(* relative addresses into real worlds are lists of integers, where []
   is the address of the base of the real world, and at each level we
   first index the real world arguments in order beginning at 1, and
   then -- in the case of a real functionality -- index the
   subfunctionalities in the lexicographic order of their names *)

type real_world_state = fun_state ILMap.t

(* addr will be None iff state is the simulator's initial state;
   otherwise, it'll be the address (type addr) of the real
   functionality being simulated *)

type sim_state = {
  addr  : form option;
  state : state
}

type ideal_world_state = {
  ideal_state       : ideal_state;
  main_sim_state    : sim_state;
  other_sims_states : sim_state list
}

(* values of type int list are relative addresses into real
   world *)

type real_world_running_context =
  | RWRC_IdealFunc of int list
  | RWRC_RealFunc  of int list *
                        symbol

type real_world_sending_context = int list

type ideal_world_running_context =
  | IWRC_Ideal_Func
  | IWRC_Main_Sim
  | IWRC_OtherSim of int  (* index (beginning at 0) into list of other
                             simulators *)

type ideal_world_sending_context =
  | IWSC_IdealFunc
  | IWSC_MainSim
  | IWSC_OtherSim of int  (* index (beginning at 0) into list of other
                             simulators *)

exception ConfigError

type config =
  | ConfigGen          of
      maps_tyd * global_context * prover_infos * worlds
  | ConfigReal         of
      maps_tyd * global_context * prover_infos * real_world *
      real_world_state
  | ConfigIdeal        of
      maps_tyd * global_context * prover_infos * ideal_world *
      ideal_world_state
  | ConfigRealRunning  of
      maps_tyd * global_context * prover_infos * real_world *
      real_world_state * real_world_running_context *
      local_context * instr_interp list located
  | ConfigIdealRunning of
      maps_tyd * global_context * prover_infos * ideal_world *
      ideal_world_state * ideal_world_running_context *
      local_context * instr_interp list located
  | ConfigRealSending  of
      maps_tyd * global_context * prover_infos * real_world *
      real_world_state * real_world_sending_context * sent_msg_expr_tyd      
  | ConfigIdealSending of
      maps_tyd * global_context * prover_infos * ideal_world *
      ideal_world_state * ideal_world_sending_context * sent_msg_expr_tyd      

let pp_config (fmt : Format.formatter) (conf : config) : unit =
  failure "fill in"

let create_config (root : symbol) (maps : maps_tyd) (env : env)
    (fe : fun_expr) : config =
  let fet = inter_check_real_fun_expr root maps fe in
  let w = fun_expr_tyd_to_worlds maps fet in
  let gc = gc_create env in
  let pi = EcProvers.dft_prover_infos in
  ConfigGen (maps, gc, pi, w)

let is_gen_config (conf : config) : bool =
  match conf with
  | ConfigGen _ -> true
  | _           -> false

let is_real_config (conf : config) : bool =
  match conf with
  | ConfigReal _ -> true
  | _            -> false

let is_ideal_config (conf : config) : bool =
  match conf with
  | ConfigIdeal _ -> true
  | _             -> false

let is_real_running_config (conf : config) : bool =
  match conf with
  | ConfigRealRunning _ -> true
  | _                   -> false

let is_ideal_running_config (conf : config) : bool =
  match conf with
  | ConfigIdealRunning _ -> true
  | _                    -> false

let is_real_sending_config (conf : config) : bool =
  match conf with
  | ConfigRealSending _ -> true
  | _                   -> false

let is_ideal_sending_config (conf : config) : bool =
  match conf with
  | ConfigIdealSending _ -> true
  | _                    -> false

let env_of_config (conf : config) : env =
  match conf with
  | ConfigGen (_, gc, _, _)                      -> env_of_gc gc
  | ConfigReal (_, gc, _, _, _)                  -> env_of_gc gc
  | ConfigIdeal (_, gc, _, _, _)                 -> env_of_gc gc
  | ConfigRealRunning (_, gc, _, _, _, _, _, _)  -> env_of_gc gc
  | ConfigIdealRunning (_, gc, _, _, _, _, _, _) -> env_of_gc gc
  | ConfigRealSending (_, gc, _, _, _, _, _)     -> env_of_gc gc
  | ConfigIdealSending (_, gc, _, _, _, _, _)    -> env_of_gc gc

let update_prover_infos_config (conf : config)
    (ppi : EcParsetree.pprover_infos) : config =
  match conf with
  | ConfigGen (maps, gc, pi, w)                                  ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigGen (maps, gc, pi, w)
  | ConfigReal (maps, gc, pi, rws, real)                         ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigReal (maps, gc, pi, rws, real)
  | ConfigIdeal (maps, gc, pi, ideal, iws)                       ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigIdeal (maps, gc, pi, ideal, iws)
  | ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)   ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)
  | ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins) ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins)
  | ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)       ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)
  | ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)     ->
      let pi = update_prover_infos (env_of_gc gc) pi ppi in
      ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)

let add_var_to_config (conf : config) (id : psymbol) (pty : pty) : config =
  match conf with
  | ConfigGen (maps, gc, pi, w)                                  ->
      let gc = gc_add_var gc id pty in
      ConfigGen (maps, gc, pi, w)
  | ConfigReal (maps, gc, pi, rws, real)                         ->
      let gc = gc_add_var gc id pty in
      ConfigReal (maps, gc, pi, rws, real)
  | ConfigIdeal (maps, gc, pi, ideal, iws)                       ->
      let gc = gc_add_var gc id pty in
      ConfigIdeal (maps, gc, pi, ideal, iws)
  | ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)   ->
      let gc = gc_add_var gc id pty in
      ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)
  | ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins) ->
      let gc = gc_add_var gc id pty in
      ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins)
  | ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)       ->
      let gc = gc_add_var gc id pty in
      ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)
  | ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)     ->
      let gc = gc_add_var gc id pty in
      ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)

let add_hyp_to_config (conf : config) (id : psymbol) (pexpr : pexpr) : config =
  match conf with
  | ConfigGen (maps, gc, pi, w)                                  ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigGen (maps, gc, pi, w)
  | ConfigReal (maps, gc, pi, rws, real)                         ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigReal (maps, gc, pi, rws, real)
  | ConfigIdeal (maps, gc, pi, ideal, iws)                       ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigIdeal (maps, gc, pi, ideal, iws)
  | ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)   ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)
  | ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins) ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins)
  | ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)       ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)
  | ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)     ->
      let gc = gc_add_hyp gc id pexpr in
      ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)

let initial_real_world_state (maps : maps_tyd) (rw : real_world)
      : real_world_state =
  let init_of_parties (pts : party_tyd IdMap.t) (addr : int list)
        : int list * fun_state =
    (addr,
     RealState
     (IdMap.map
      (fun (pt : party_tyd) ->
         state_no_args (initial_state_id_of_party_tyd pt))
      pts)) in
  let init_of_subfuns (subs : symb_pair IdMap.t) (nargs : int)
      (addr : int list) : (int list * fun_state) list =
    let sps = List.map snd (IdMap.bindings subs) in
    List.mapi
    (fun i sp ->
       (addr @ [1 + nargs + i],
        IdealState
         (state_no_args
          (initial_state_id_of_ideal_fun_tyd
           (IdPairMap.find sp maps.fun_map)))))
    sps in
  let rec init_of_rw ((sp, _, rwas) : real_world) (addr : int list)
        : (int list * fun_state) list =
    let rfbt =
      real_fun_body_tyd_of (unloc (IdPairMap.find sp maps.fun_map)) in
    [init_of_parties rfbt.parties addr] @
    init_of_subfuns rfbt.sub_funs (IdMap.cardinal rfbt.params) addr @
    List.concat
    (List.mapi (fun i rwa -> init_of_rwa rwa (addr @ [i + 1])) rwas)
  and init_of_rwa (rwa : real_world_arg) (addr : int list)
        : (int list * fun_state) list =
    match rwa with
    | RWA_Real rw       -> init_of_rw rw addr
    | RWA_Ideal (sp, _) ->
        [(addr,
          IdealState
          (state_no_args
           (initial_state_id_of_ideal_fun_tyd
            (IdPairMap.find sp maps.fun_map))))] in
  let bindings = init_of_rw rw [] in
  List.fold_left
  (fun mp (addr, fs) -> ILMap.add addr fs mp)
  ILMap.empty bindings

let real_of_gen_config (conf : config) : config =
  match conf with
  | ConfigGen (maps, gc, pi, w) ->
      let states = initial_real_world_state maps w.worlds_real in
      ConfigReal (maps, gc, pi, w.worlds_real, states)
  | _                           -> raise ConfigError

let initial_ideal_world_state (maps : maps_tyd) (iw : ideal_world)
      : ideal_world_state =
  let ideal_state =
    state_no_args
    (initial_state_id_of_ideal_fun_tyd
     (IdPairMap.find (fst iw.iw_ideal_func) maps.fun_map)) in
  let main_sim_state =
    {addr  = None;
     state =
       state_no_args
       (initial_state_id_of_sim_tyd
        (IdPairMap.find (proj3_1 iw.iw_main_sim) maps.sim_map))} in
  let other_sims_states =
    List.map
    (fun (sp, _, _) ->
       {addr  = None;
        state =
          state_no_args
          (initial_state_id_of_sim_tyd
           (IdPairMap.find sp maps.sim_map))})
    iw.iw_other_sims in
  {ideal_state       = ideal_state;
   main_sim_state    = main_sim_state;
   other_sims_states = other_sims_states}

let ideal_of_gen_config (conf : config) : config =
  match conf with
  | ConfigGen (maps, gc, pi, w) ->
      let pi = EcProvers.dft_prover_infos in
      let iws = initial_ideal_world_state maps w.worlds_ideal in
      ConfigIdeal (maps, gc, pi, w.worlds_ideal, iws)
  | _                           -> raise ConfigError

let loc_of_running_config_next_instr (conf : config) : EcLocation.t option =
  match conf with
  | ConfigRealRunning (_, _, _, _, _, _, _, ins)  -> Some (loc ins)
  | ConfigIdealRunning (_, _, _, _, _, _, _, ins) -> Some (loc ins)
  | _                                             -> None

(* sending messages and stepping configurations *)

type effect =
  | EffectOK                           (* step succeeded (not random
                                          assignment), and new configuration
                                          is running or internal send *)
  | EffectRand of EcIdent.t            (* step added ident representing
                                          random choice to global context,
                                          and new configuration is
                                          running *)
  | EffectMsgOut of sent_msg_expr_tyd  (* a message was output, and new
                                          configuration is real or ideal *)
  | EffectFailOut                      (* fail was output, and new
                                          configuration is real or ideal *)
  | EffectBlockedIf                    (* configuration is running *)
  | EffectBlockedMatch                 (* configuration is running *)
  | EffectBlockedPortOfAddrCompare     (* configuration is sending *)

let send_message_to_real_or_ideal_config
    (conf : config) (sme : sent_msg_expr_tyd) : config * effect =
  match conf with
  | ConfigReal (maps, gc, pi, rws, real)   ->
      failure "fill in"
  | ConfigIdeal (maps, gc, pi, ideal, iws) ->
      failure "fill in"
  | _                                      -> raise ConfigError

let step_running_or_sending_real_or_ideal_config
    (conf : config) : config * effect =
  match conf with
  | ConfigRealRunning (maps, gc, pi, real, rws, rwrc, lc, ins)   ->
      failure "fill in"
  | ConfigIdealRunning (maps, gc, pi, ideal, iws, iwrc, lc, ins) ->
      failure "fill in"
  | ConfigRealSending (maps, gc, pi, real, rws, rwsc, sme)       ->
      failure "fill in"
  | ConfigIdealSending (maps, gc, pi, ideal, iws, iwsc, sme)     ->
      failure "fill in"
  | _                                                            ->
      raise ConfigError
