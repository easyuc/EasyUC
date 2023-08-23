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

module Int =  (* domain: int *)
  struct
    type t = int
    let compare = (Stdlib.compare : t -> t -> int)
  end

module IntSet = Set.Make(Int)

type worlds = {
  worlds_real  : real_world;
  worlds_ideal : ideal_world
}

(* compute the adversarial port indices of a world that the environment
   -- when communicating with the adversary / simulators + adversary --
   may *not* communicate with *)

let interface_input_guard_exclusion_of_ideal_world (iw : ideal_world)
      : IntSet.t =
  IntSet.union
  (IntSet.singleton (proj3_2 iw.iw_main_sim))
  (IntSet.of_list (List.map (fun (_, i, _) -> i) iw.iw_other_sims))

let interface_input_guard_exclusion_of_worlds (w : worlds) : IntSet.t =
  interface_input_guard_exclusion_of_ideal_world w.worlds_ideal

let pp_int (ppf : formatter) (i : int) : unit =
  fprintf ppf "%d" i

let pp_paren_int_list (ppf : formatter) (is : int list) : unit =
  if List.is_empty is
  then ()
  else fprintf ppf "(@[%a@])"
       (EcPrinting.pp_list ",@ " pp_int) is

let pp_symb_pair_int (ppf : formatter) (sp, i : symb_pair * int)
      : unit =
  fprintf ppf "@[%s.%s:%i@]" (fst sp) (snd sp) i

let pp_symb_pair_int_int_list
    (ppf : formatter) (sp, i, is : symb_pair * int * int list)
      : unit =
  fprintf ppf "@[%s.%s:%i@,%a@]" (fst sp) (snd sp) i
  pp_paren_int_list is

let pp_worlds (ppf : formatter) (w : worlds) : unit =
  let rec pp_real_world (ppf : formatter) (rw : real_world) : unit =
    let sp, i, rwas = rw in
    match rwas with
    | [] ->
      fprintf ppf "@[%a@]"
      pp_symb_pair_int (sp, i)
    | _  ->
      fprintf ppf "@[%a@,(@[%a@])@]"
      pp_symb_pair_int (sp, i)
      (EcPrinting.pp_list ",@ " pp_real_world_arg) rwas

  and pp_real_world_arg (ppf : formatter) (rwa : real_world_arg)
        : unit =
    match rwa with
    | RWA_Real rw       -> fprintf ppf "%a" pp_real_world rw
    | RWA_Ideal (sp, i) -> fprintf ppf "%a" pp_symb_pair_int (sp, i) in

  let rec pp_sims (ppf : formatter)
          (spis : (symb_pair * int * int list) list) : unit =
    match spis with
    | []        -> ()
    | [spi]     ->
      fprintf ppf " *@ %a"
      pp_symb_pair_int_int_list spi
    | spi :: spis ->
      fprintf ppf " *@ %a%a"
      pp_symb_pair_int_int_list spi
      pp_sims spis in

  let pp_ideal_world (ppf : formatter) (iw : ideal_world) : unit =
    fprintf ppf "@[%a /@ @[%a%a@]@]"
    pp_symb_pair_int iw.iw_ideal_func
    pp_symb_pair_int_int_list iw.iw_main_sim
    pp_sims iw.iw_other_sims in

  fprintf ppf "@[%a ~@ %a@]@."
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

let pp_local_context (env : env) (ppf : formatter) (lc : local_context) : unit =
  let pp_frame_entry (ppf : formatter) ((id, form) : EcIdent.t * form)
        : unit =
    fprintf ppf "@[%a :@ %a@]"
    EcIdent.pp_ident id
    (pp_form env) form in
  let pp_frame (ppf : formatter) (frame : form EcIdent.Mid.t) : unit =
    EcPrinting.pp_list ",@ " pp_frame_entry ppf
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
  let env = env_of_gc gc in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pp_loc (ppf : formatter) (id, lk) : unit =
    match lk with
    | EcBaseLogic.LD_var (ty, _) ->
        fprintf ppf "@[%a :@ @[%a@]@]"
        EcIdent.pp_ident id
        (EcPrinting.pp_type ppe) ty
    | EcBaseLogic.LD_hyp form    ->
        fprintf ppf "@[%a :@ @[%a@]@]"
        EcIdent.pp_ident id
        (EcPrinting.pp_form ppe) form
    | _                          -> failure "cannot happen" in
  let locs = List.rev (LDecl.tohyps gc).h_local in
  fprintf ppf "@[%a@]"
  (EcPrinting.pp_list ",@ " pp_loc) locs

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
      (fun ppf -> fprintf ppf "@[prover infos error: %s@]" s)

let default_prover_infos (env : EcEnv.env) : prover_infos =
  {EcProvers.dft_prover_infos with
     pr_provers =
       List.filter EcProvers.is_prover_known
       EcProvers.dft_prover_names;
     pr_timelimit = 1}

(* making formulas for use in SMT applications *)

let env_root_addr_form : form = form_of_expr mhr env_root_addr_op

let env_root_port_form : form = form_of_expr mhr env_root_port_op

let envport_form (func : form) (adv : form) (pt : form) : form =
  f_app (form_of_expr mhr envport_op) [func; adv; pt] tbool

let inc_form (addr1 : form) (addr2 : form) : form =
  f_app (form_of_expr mhr inc_op) [addr1; addr2] tbool

let addr_le_form (addr1 : form) (addr2 : form) : form =
  f_app (form_of_expr mhr addr_le_op) [addr1; addr2] tbool

let addr_lt_form (addr1 : form) (addr2 : form) : form =
  f_app (form_of_expr mhr addr_lt_op) [addr1; addr2] tbool

let addr_concat_form (addr1 : form) (addr2 : form) : form =
  f_app (form_of_expr mhr addr_concat_op) [addr1; addr2] addr_ty

let addr_nil_form : form = form_of_expr mhr addr_nil_op

let addr_cons_form (n : form) (addr : form) : form =
  f_app (form_of_expr mhr addr_cons_op) [n; addr] addr_ty

let addr_make_form (ms : int list) : form =
  List.fold_right
  (fun m exp -> addr_cons_form (f_int (EcBigInt.of_int m)) exp)
  ms addr_nil_form

let port_to_addr_form (port : form) : form =
  f_proj port 0 addr_ty

let port_to_pi_form (port : form) : form =
  f_proj port 1 tint

let make_port (addr : form) (pi : form) : form =
  f_tuple [addr; pi]

let int_form (n : int) : form = f_int (EcBigInt.of_int n)

let int_add_form (n1 : form) (n2 : form) : form =
  f_app (form_of_expr mhr int_add_op) [n1; n2] tint

let int_lt_form (n1 : form) (n2 : form) : form =
  f_app (form_of_expr mhr int_lt_op) [n1; n2] tbool

let int_le_form (n1 : form) (n2 : form) : form =
  f_app (form_of_expr mhr int_le_op) [n1; n2] tbool

let int_memb_of_fset_form (n : form) (ms : IntSet.t) : form =
  IntSet.fold
  (fun m f ->
     (f_or
      (f_eq n (f_int (EcBigInt.of_int m)))
      f))
  ms
  f_false

(* SMT applications *)

exception SMT_Test

let eval_bool_form_to_bool (gc : global_context) (pi : prover_infos)
    (f : form) : bool =
  let () =
    debugging_message
    (fun ppf ->
       fprintf ppf
       ("@[@[using@ SMT@ to@ determine@ truth@ or@ falsity@ " ^^
        "of:@]@\n@\n@[%a@]@]@.")
       (pp_form (env_of_gc gc)) f) in
  match UcEcFormEval.eval_condition gc f pi with
  | UcEcFormEval.Bool b    ->
      (if b
       then debugging_message
            (fun ppf -> fprintf ppf "@[formula@ proved@]@.")
       else debugging_message
            (fun ppf -> fprintf ppf "@[formula's@ negation@ proved@]@."));
      b
  | UcEcFormEval.Undecided ->
      (debugging_message
       (fun ppf ->
          fprintf ppf "@[unable@ to@ prove@ formula@ or@ its@ negation@]@."));
      raise SMT_Test

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

let real_state_of_fun_state (fs : fun_state) : real_state =
  match fs with
  | RealState rs -> rs
  | IdealState _ -> failure "should not happen"

let ideal_state_of_fun_state (fs : fun_state) : ideal_state =
  match fs with
  | RealState _   -> failure "should not happen"
  | IdealState is -> is

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
  ideal_fun_state   : ideal_state;
  main_sim_state    : sim_state;
  other_sims_states : sim_state list
}

type control =  (* does environment or adversary have control? *)
  | CtrlEnv
  | CtrlAdv

let pp_control (ppf : formatter) (ctrl : control) : unit =
  match ctrl with
  | CtrlEnv -> fprintf ppf "environment"
  | CtrlAdv -> fprintf ppf "adversary"

(* values of type int list are relative addresses into real
   world *)

type real_world_running_context =
  | RWRC_IdealFunc of int list *
                      symb_pair    (* functionality *)
  | RWRC_RealFunc  of int list  *
                      symb_pair *  (* functionality *)
                      symbol       (* party name *)

let pp_relative_address (ppf : formatter) (addr : int list) : unit =
  fprintf ppf "[@[%a@]]"
  (EcPrinting.pp_list ",@ " pp_int) addr

let pp_symb_pair (ppf : formatter) (sp : symb_pair) : unit =
  fprintf ppf "%s.%s" (fst sp) (snd sp)

let pp_real_world_running_context (ppf : formatter)
    (rwrc : real_world_running_context) : unit =
  match rwrc with
  | RWRC_IdealFunc (is, sp)       ->
      fprintf ppf "@[running at %a: %a@]"
      pp_relative_address is
      pp_symb_pair sp
  | RWRC_RealFunc (is, sp, pty) ->
      fprintf ppf "@[running at %a: %a: %s@]"
      pp_relative_address is
      pp_symb_pair sp
      pty

type real_world_sending_context =
  | RWSC_Env                     (* sending from environment *)
  | RWSC_Adv                     (* sending from adversary *)
  | RWSC_FromFunc of int list *  (* relative address *)
                     symb_pair   (* functionality *)

let pp_real_world_sending_context (ppf : formatter)
    (rwsc : real_world_sending_context) : unit =
  match rwsc with
  | RWSC_Env               ->
      fprintf ppf "@[sending from environment@]"
  | RWSC_Adv               ->
      fprintf ppf "@[sending from adversary@]"
  | RWSC_FromFunc (is, sp) ->
      fprintf ppf "@[sending from %a: %a@]"
      pp_relative_address is
      pp_symb_pair sp

type ideal_world_running_context =
  | IWRC_Ideal_Func of symb_pair *  (* functionality *)
                       int          (* adversarial port index *)
  | IWRC_Main_Sim   of symb_pair *  (* main simulator *)
                       int          (* adversarial port index *)
  | IWRC_OtherSim   of symb_pair *  (* other simulator *)
                       int       *  (* adversarial port index *)
                       int          (* index (from 0) into list of
                                       other simulators *)

let pp_ideal_world_running_context (ppf : formatter)
    (iwrc : ideal_world_running_context) : unit =
  match iwrc with
  | IWRC_Ideal_Func (sp, i)  ->
      fprintf ppf "@[running at %a:%n@]"
      pp_symb_pair sp
      i
  | IWRC_Main_Sim (sp, i)    ->
      fprintf ppf "@[running at %a:%n@]"
      pp_symb_pair sp
      i
  | IWRC_OtherSim (sp, i, _) ->
      fprintf ppf "@[running at %a:%n@]"
      pp_symb_pair sp
      i

type ideal_world_sending_context =
  | IWSC_Env                        (* sending from environment *)
  | IWSC_Adv                        (* sending from adversary *)
  | IWSC_Ideal_Func of symb_pair *  (* functionality *)
                       int          (* adversarial port index *)
  | IWSC_Main_Sim   of symb_pair *  (* main simulator *)
                       int          (* adversarial port index *)
  | IWSC_OtherSim   of symb_pair *  (* other simulator *)
                       int       *  (* adversarial port index *)
                       int          (* index (from 0) into list of
                                       other simulators *)

let pp_ideal_world_sending_context (ppf : formatter)
    (iwrc : ideal_world_sending_context) : unit =
  match iwrc with
  | IWSC_Env                 ->
      fprintf ppf "@[sending from environment@]"
  | IWSC_Adv                 ->
      fprintf ppf "@[sending from adversary@]"
  | IWSC_Ideal_Func (sp, i)  ->
      fprintf ppf "@[sending from %a:%n@]"
      pp_symb_pair sp
      i
  | IWSC_Main_Sim (sp, i)    ->
      fprintf ppf "@[sending from %a:%n@]"
      pp_symb_pair sp
      i
  | IWSC_OtherSim (sp, i, _) ->
      fprintf ppf "@[sending from %a:%n@]"
      pp_symb_pair sp
      i

type config_gen = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  w    : worlds;
  ig   : IntSet.t  (* input guard of interface *)
}

type config_real = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  rw   : real_world;
  ig   : IntSet.t;
  rws  : real_world_state;
  ctrl : control;
}

type config_ideal = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  iw   : ideal_world;
  ig   : IntSet.t;
  iws  : ideal_world_state;
  ctrl : control;
}

type config_real_running = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  rw   : real_world;
  ig   : IntSet.t;
  rws  : real_world_state;
  rwrc : real_world_running_context;
  lc   : local_context;
  ins  : instr_interp list located
}

type config_ideal_running = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  iw   : ideal_world;
  ig   : IntSet.t;
  iws  : ideal_world_state;
  iwrc : ideal_world_running_context;
  lc   : local_context;
  ins  : instr_interp list located
}

type config_real_sending = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  rw   : real_world;
  ig   : IntSet.t;
  rws  : real_world_state;
  rwsc : real_world_sending_context;
  sme  : sent_msg_expr_tyd
}

type config_ideal_sending = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  iw   : ideal_world;
  ig   : IntSet.t;
  iws  : ideal_world_state;
  iwsc : ideal_world_sending_context;
  sme  : sent_msg_expr_tyd
}

type config =
  | ConfigGen          of config_gen
  | ConfigReal         of config_real
  | ConfigIdeal        of config_ideal
  | ConfigRealRunning  of config_real_running
  | ConfigIdealRunning of config_ideal_running
  | ConfigRealSending  of config_real_sending
  | ConfigIdealSending of config_ideal_sending

exception ConfigError

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
  | ConfigGen c          -> env_of_gc c.gc
  | ConfigReal c         -> env_of_gc c.gc
  | ConfigIdeal c        -> env_of_gc c.gc
  | ConfigRealRunning c  -> env_of_gc c.gc
  | ConfigIdealRunning c -> env_of_gc c.gc
  | ConfigRealSending c  -> env_of_gc c.gc
  | ConfigIdealSending c -> env_of_gc c.gc

let control_of_real_or_ideal_config (conf : config) : control =
  match conf with
  | ConfigReal c  -> c.ctrl
  | ConfigIdeal c -> c.ctrl
  | _             -> raise ConfigError

let loc_of_running_config_next_instr (conf : config) : EcLocation.t option =
  match conf with
  | ConfigRealRunning c  -> Some (loc c.ins)
  | ConfigIdealRunning c -> Some (loc c.ins)
  | _                    -> None

(* pretty printer for configurations *)

let party_and_sub_fun_states (maps : maps_tyd) (rws : real_world_state)
    (addr : int list) (sp : symb_pair) : (symbol * state) list =
  let rfbt = real_fun_body_tyd_of (unloc (IdPairMap.find sp maps.fun_map)) in
  let num_args = IdMap.cardinal rfbt.params in
  let of_parties =
    IdMap.bindings (real_state_of_fun_state (ILMap.find addr rws)) in
  let of_sub_funs =
    List.mapi
    (fun i id ->
       (id,
        ideal_state_of_fun_state
        (ILMap.find (addr @ [1 + num_args + i]) rws)))
    (List.map fst (IdMap.bindings rfbt.sub_funs)) in
  of_parties @ of_sub_funs

let pp_state (gc : global_context) (ppf : formatter)
    (state : state) : unit =
  let env = env_of_gc gc in
  match state.args with
  | []   -> fprintf ppf "%s" state.id
  | args ->
      fprintf ppf "@[%s@,(@[%a@])@]" state.id
      (EcPrinting.pp_list ",@ " (pp_form env)) args

let pp_sym_state (gc : global_context) (ppf : formatter)
    ((id, state) : symbol * state) : unit =
  fprintf ppf "@[%s:@ %a@]" id (pp_state gc) state

let pp_sym_state_list (gc : global_context) (ppf : formatter)
    (sym_stat_list : (symbol * state) list) : unit =
  EcPrinting.pp_list ",@ " (pp_sym_state gc) ppf sym_stat_list

let pp_real_world_with_states (maps : maps_tyd) (gc : global_context)
    (rws : real_world_state) (ppf : formatter) (rw : real_world) : unit =
  let rec pp_real_world (addr : int list) (ppf : formatter)
      ((sp, i, rwas) : real_world) : unit =
    let psfs = party_and_sub_fun_states maps rws addr sp in
    match rwas with
    | [] ->
      fprintf ppf "@[%a@,[@[%a@]]@]"
      pp_symb_pair_int (sp, i) (pp_sym_state_list gc) psfs
    | _  ->
      fprintf ppf "@[%a@,[@[%a@]]@,(@[%a@])@]"
      pp_symb_pair_int (sp, i) (pp_sym_state_list gc) psfs
      (pp_real_world_args 1 addr) rwas

  and pp_real_world_args (i : int) (addr : int list)
      (ppf : formatter) (rwas : real_world_arg list) : unit =
    match rwas with
    | []          -> failure "cannot happen"
    | [rwa]       ->
      fprintf ppf "%a"
      (pp_real_world_arg (addr @ [i])) rwa
    | rwa :: rwas ->
      fprintf ppf "%a,@ %a"
      (pp_real_world_arg (addr @ [i])) rwa
      (pp_real_world_args (i + 1) addr) rwas

  and pp_real_world_arg (addr : int list) (ppf : formatter)
      (rwa : real_world_arg) : unit =
    match rwa with
    | RWA_Real rw       -> pp_real_world addr ppf rw
    | RWA_Ideal (sp, i) ->
        let ideal_st = ideal_state_of_fun_state (ILMap.find addr rws) in
        fprintf ppf "%a@,[@[%a@]]"
        pp_symb_pair_int (sp, i)
        (pp_state gc) ideal_st in
  pp_real_world [] ppf rw

let pp_sim_state (gc : global_context) (iws : ideal_world_state)
    (ppf : formatter) (sim_st : sim_state) : unit =
  let ppe = EcPrinting.PPEnv.ofenv (env_of_gc gc) in
  let pp_addr (ppf : formatter) (f_opt : form option) : unit =
    match f_opt with
    | None   -> fprintf ppf "uninitialzed"
    | Some f ->
        fprintf ppf "@[initialized:@ %a@]"
        (EcPrinting.pp_form ppe) f in
  fprintf ppf "@[%a/%a@]"
  pp_addr sim_st.addr
  (pp_state gc) sim_st.state

let rec pp_sims_with_states (i : int) (gc : global_context)
    (iws : ideal_world_state) (ppf : formatter)
    (spis : (symb_pair * int * int list) list) : unit =
  match spis with
  | []        -> ()
  | [spi]     ->
    fprintf ppf " *@ %a@,[@[%a@]]"
    pp_symb_pair_int_int_list spi
    (pp_sim_state gc iws) (List.nth iws.other_sims_states i)
  | spi :: spis ->
    fprintf ppf " *@ %a@,[@[%a@]]%a"
    pp_symb_pair_int_int_list spi
    (pp_sim_state gc iws) (List.nth iws.other_sims_states i)
    (pp_sims_with_states (i + 1) gc iws) spis

let pp_ideal_world_with_states (maps : maps_tyd) (gc : global_context)
    (iws : ideal_world_state) (ppf : formatter) (iw : ideal_world) : unit =
  fprintf ppf "@[%a@,[@[%a]@] /@ @[%a@,[@[%a@]]%a@]@]"
  pp_symb_pair_int iw.iw_ideal_func
  (pp_state gc) iws.ideal_fun_state
  pp_symb_pair_int_int_list iw.iw_main_sim
  (pp_sim_state gc iws) iws.main_sim_state
  (pp_sims_with_states 0 gc iws) iw.iw_other_sims

let pp_int_set (ppf : formatter) (is : IntSet.t) : unit =
  let is = IntSet.elements is in
  fprintf ppf "@[%a@]"
  (EcPrinting.pp_list ",@ " pp_int) is

let pp_global_context_msg (ppf : formatter) (gc : global_context) : unit =
  fprintf ppf
  "@[global context:@ %a@]"
  pp_gc gc

let pp_worlds_msg (ppf : formatter) (w : worlds) : unit =
  fprintf ppf
  "@[worlds:@ %a@]"
  pp_worlds w

let pp_real_world_with_states_msg (maps : maps_tyd) (gc : global_context)
    (rws : real_world_state) (ppf : formatter) (rw : real_world) : unit =
  fprintf ppf
  "@[real world:@ %a@]"
  (pp_real_world_with_states maps gc rws) rw

let pp_ideal_world_with_states_msg (maps : maps_tyd) (gc : global_context)
    (iws : ideal_world_state) (ppf : formatter) (iw : ideal_world) : unit =
  fprintf ppf
  "@[ideal world:@ %a@]"
  (pp_ideal_world_with_states maps gc iws) iw

let pp_input_guard_msg (ppf : formatter) (is : IntSet.t) : unit =
  fprintf ppf
  "@[input guard exclusion:@ %a@]"
  pp_int_set is

let pp_control_msg (ppf : formatter) (ctrl : control) : unit =
  fprintf ppf
  "@[control:@ %a@]"
  pp_control ctrl

let pp_config (ppf : formatter) (conf : config) : unit =
  match conf with
  | ConfigGen c          ->
      fprintf ppf
      "@[%a@\n@\n%a@]"
      pp_global_context_msg c.gc
      pp_worlds_msg c.w
  | ConfigReal c         ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@]"
      pp_global_context_msg c.gc
      (pp_real_world_with_states_msg c.maps c.gc c.rws) c.rw
      pp_input_guard_msg c.ig
      pp_control_msg c.ctrl
  | ConfigIdeal c        ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@]"
      pp_global_context_msg c.gc
      (pp_ideal_world_with_states_msg c.maps c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_control_msg c.ctrl
  | ConfigRealRunning c  ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n@\n%a@]"
      pp_global_context_msg c.gc
      (pp_real_world_with_states_msg c.maps c.gc c.rws) c.rw
      pp_input_guard_msg c.ig
      pp_real_world_running_context c.rwrc
      (pp_local_context (env_of_gc c.gc)) c.lc
  | ConfigIdealRunning c ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n@\n%a@]"
      pp_global_context_msg c.gc
      (pp_ideal_world_with_states_msg c.maps c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_ideal_world_running_context c.iwrc
      (pp_local_context (env_of_gc c.gc)) c.lc
  | ConfigRealSending c  ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n@\n@[message:@ %a@]@]"
      pp_global_context_msg c.gc
      (pp_real_world_with_states_msg c.maps c.gc c.rws) c.rw
      pp_input_guard_msg c.ig
      pp_real_world_sending_context c.rwsc
      (pp_sent_msg_expr_tyd (env_of_gc c.gc)) c.sme
  | ConfigIdealSending c ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n@\nmessage:@ %a@@]"
      pp_global_context_msg c.gc
      (pp_ideal_world_with_states_msg c.maps c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_ideal_world_sending_context c.iwsc
      (pp_sent_msg_expr_tyd (env_of_gc c.gc)) c.sme

let pp_sent_msg_expr_tyd_in_config (ppf : formatter) (c : config)
    (sme : sent_msg_expr_tyd) : unit =
  pp_sent_msg_expr_tyd (env_of_config c) ppf sme

let create_gen_config (root : symbol) (maps : maps_tyd) (env : env)
    (fe : fun_expr) : config =
  let fet = inter_check_real_fun_expr root maps fe in
  let w = fun_expr_tyd_to_worlds maps fet in
  let ig = interface_input_guard_exclusion_of_worlds w in
  let gc = gc_create env in
  let pi = default_prover_infos env in
  ConfigGen {maps = maps; gc = gc; pi = pi; w = w; ig = ig}

let update_prover_infos_config (conf : config)
    (ppi : EcParsetree.pprover_infos) : config =
  match conf with
  | ConfigGen c          ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigGen {c with pi = pi}
  | ConfigReal c         ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigReal {c with pi = pi}
  | ConfigIdeal c        ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigIdeal {c with pi = pi}
  | ConfigRealRunning c  ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigRealRunning {c with pi = pi}
  | ConfigIdealRunning c ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigIdealRunning {c with pi = pi}
  | ConfigRealSending c  ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigRealSending {c with pi = pi}
  | ConfigIdealSending c ->
      let pi = update_prover_infos (env_of_gc c.gc) c.pi ppi in
      ConfigIdealSending {c with pi = pi}

let add_var_to_config (conf : config) (id : psymbol) (pty : pty) : config =
  match conf with
  | ConfigGen c          ->
      let gc = gc_add_var c.gc id pty in
      ConfigGen {c with gc = gc}
  | ConfigReal c         ->
      let gc = gc_add_var c.gc id pty in
      ConfigReal {c with gc = gc}
  | ConfigIdeal c        ->
      let gc = gc_add_var c.gc id pty in
      ConfigIdeal {c with gc = gc}
  | ConfigRealRunning c  ->
      let gc = gc_add_var c.gc id pty in
      ConfigRealRunning {c with gc = gc}
  | ConfigIdealRunning c ->
      let gc = gc_add_var c.gc id pty in
      ConfigIdealRunning {c with gc = gc}
  | ConfigRealSending c  ->
      let gc = gc_add_var c.gc id pty in
      ConfigRealSending {c with gc = gc}
  | ConfigIdealSending c ->
      let gc = gc_add_var c.gc id pty in
      ConfigIdealSending {c with gc = gc}

let add_hyp_to_config (conf : config) (id : psymbol) (pexpr : pexpr) : config =
  match conf with
  | ConfigGen c          ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigGen {c with gc = gc}
  | ConfigReal c         ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigReal {c with gc = gc}
  | ConfigIdeal c        ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigIdeal {c with gc = gc}
  | ConfigRealRunning c  ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigRealRunning {c with gc = gc}
  | ConfigIdealRunning c ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigIdealRunning {c with gc = gc}
  | ConfigRealSending c  ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigRealSending {c with gc = gc}
  | ConfigIdealSending c ->
      let gc = gc_add_hyp c.gc id pexpr in
      ConfigIdealSending {c with gc = gc}

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
  | ConfigGen c ->
      let rw = c.w.worlds_real in
      let rws = initial_real_world_state c.maps rw in
      ConfigReal
      {maps = c.maps; gc = c.gc; pi = c.pi; rw = rw; ig = c.ig;
       rws = rws; ctrl = CtrlEnv}
  | _           -> raise ConfigError

let initial_ideal_world_state (maps : maps_tyd) (iw : ideal_world)
      : ideal_world_state =
  let ideal_fun_state =
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
  {ideal_fun_state   = ideal_fun_state;
   main_sim_state    = main_sim_state;
   other_sims_states = other_sims_states}

let ideal_of_gen_config (conf : config) : config =
  match conf with
  | ConfigGen c ->
      let iw = c.w.worlds_ideal in
      let iws = initial_ideal_world_state c.maps iw in
      ConfigIdeal
      {maps = c.maps; gc = c.gc; pi = c.pi; iw = iw; ig = c.ig;
       iws = iws; ctrl = CtrlEnv}
  | _           -> raise ConfigError

(* sending messages and stepping configurations *)

type effect =
  | EffectOK                           (* step succeeded (not random
                                          assignment), and new configuration
                                          is running or sending *)
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
  | EffectBlockedPortOrAddrCompare     (* configuration is running or sending *)

let pp_effect (ppf : formatter) (c : config) (e : effect) : unit =
  let env = env_of_config c in
  match e with
  | EffectOK                       -> fprintf ppf "EffectOK"
  | EffectRand id                  ->
      fprintf ppf "EffectRand: %a"
      EcIdent.pp_ident id
  | EffectMsgOut sme               ->
      fprintf ppf "EffectMsgOut: %a"
      (pp_sent_msg_expr_tyd env) sme
  | EffectFailOut                  -> fprintf ppf "EffectFailOut"
  | EffectBlockedIf                -> fprintf ppf "EffectBlockedIf"
  | EffectBlockedMatch             -> fprintf ppf "EffectBlockedMatch"
  | EffectBlockedPortOrAddrCompare ->
      fprintf ppf "EffectBlockedPortOrAddrCompare"

let fail_out_of_running_or_sending_config (conf : config) : config * effect =
  match conf with
  | ConfigRealRunning c  ->
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; rw = c.rw; ig = c.ig; rws = c.rws;
        ctrl = CtrlEnv},
       EffectFailOut)
  | ConfigIdealRunning c ->
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; iw = c.iw; ig = c.ig; iws = c.iws;
        ctrl = CtrlEnv},
       EffectFailOut)
  | ConfigRealSending c  ->
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; rw = c.rw; ig = c.ig; rws = c.rws;
        ctrl = CtrlEnv},
       EffectFailOut)
  | ConfigIdealSending c ->
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; iw = c.iw; ig = c.ig; iws = c.iws;
        ctrl = CtrlEnv},
       EffectFailOut)
  | _                    -> raise ConfigError

let fill_in (str : string) (conf : config) : config * effect =
  Printf.eprintf "warning: to be filled in: %s\n\n" str;
  fail_out_of_running_or_sending_config conf

let msg_out_of_sending_config (conf : config) (ctrl : control)
      : config * effect =
  match conf with
  | ConfigRealSending c  ->
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; rw = c.rw; ig = c.ig; rws = c.rws;
        ctrl = ctrl},
       EffectMsgOut c.sme)
  | ConfigIdealSending c ->
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; iw = c.iw; ig = c.ig; iws = c.iws;
        ctrl = ctrl},
       EffectMsgOut c.sme)
  | _                    -> raise ConfigError

let send_message_to_real_or_ideal_config
    (conf : config) (sme : sent_msg_expr) : config =
  match conf with
  | ConfigReal c  ->
      let sme = inter_check_sent_msg_expr c.maps (env_of_gc c.gc) sme in
      ConfigRealSending
      {maps = c.maps;
       gc   = c.gc;
       pi   = c.pi;
       rw   = c.rw;
       ig   = c.ig;
       rws  = c.rws;
       rwsc = if c.ctrl = CtrlEnv then RWSC_Env else RWSC_Adv;
       sme  = sme}
  | ConfigIdeal c ->
      let sme = inter_check_sent_msg_expr c.maps (env_of_gc c.gc) sme in
      ConfigIdealSending
      {maps = c.maps;
       gc   = c.gc;
       pi   = c.pi;
       iw   = c.iw;
       ig   = c.ig;
       iws  = c.iws;
       iwsc = if c.ctrl = CtrlEnv then IWSC_Env else IWSC_Adv;
       sme  = sme}
  | _             -> raise ConfigError

let step_real_running_config (rc : config_real_running) : config * effect =
  fill_in "step_real_running_config" (ConfigRealRunning rc)

let step_ideal_running_config (c : config_ideal_running) : config * effect =
  fill_in "step_real_running_config" (ConfigIdealRunning c)

let step_real_sending_config (c : config_real_sending) : config * effect =
  let mode = mode_of_sent_msg_expr_tyd c.sme in
  let dest_port = dest_port_of_sent_msg_expr_tyd c.sme in
  let dest_addr = port_to_addr_form dest_port in
  let dest_pi = port_to_pi_form dest_port in
  let source_port = source_port_of_sent_msg_expr_tyd c.sme in

  let from_env () =
    if mode = Dir &&
       eval_bool_form_to_bool c.gc c.pi
       (f_and
        (f_eq func_form dest_addr)
        (envport_form func_form adv_form source_port))
      then fill_in "should go to real running" (ConfigRealSending c)
    else if mode = Adv &&
            eval_bool_form_to_bool c.gc c.pi
            (f_and
             (f_eq dest_addr adv_form)
              (f_or
               (f_and
                (f_eq dest_pi (int_form 0))
                (f_eq source_port env_root_port_form))
               (f_and
                (int_lt_form (int_form 0) dest_pi)
                (f_and
                 (f_not (int_memb_of_fset_form dest_pi c.ig))
                 (envport_form func_form adv_form source_port)))))
      then msg_out_of_sending_config (ConfigRealSending c) CtrlAdv
    else fail_out_of_running_or_sending_config (ConfigRealSending c) in

  let from_adv () =
    fill_in "message from adv" (ConfigRealSending c) in

  let from_func () =
    fill_in "message from func" (ConfigRealSending c) in

  try
    match c.rwsc with
    | RWSC_Env               -> from_env ()
    | RWSC_Adv               -> from_adv ()
    | RWSC_FromFunc (is, sp) -> from_func ()
  with
  | SMT_Test ->
      (ConfigRealSending c, EffectBlockedPortOrAddrCompare)

let step_ideal_sending_config (c : config_ideal_sending) : config * effect =
  fill_in "trying to step ideal sending config" (ConfigIdealSending c)

let step_running_or_sending_real_or_ideal_config
    (conf : config) : config * effect =
  match conf with
  | ConfigRealRunning c  -> step_real_running_config c
  | ConfigIdealRunning c -> step_ideal_running_config c
  | ConfigRealSending c  -> step_real_sending_config c
  | ConfigIdealSending c -> step_ideal_sending_config c
  | _                    -> raise ConfigError
