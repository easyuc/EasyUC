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

(* the values of type int in a real world are the base adversarial
   port indices of the instances of the units of real or ideal
   functionalities

   with a real functionality, it will be the adversarial port index
   that the ideal functionality of the unit uses to communicate with
   its simulator in the ideal world (note that this ideal
   functionality will be implicit - an argument of the application of
   the real functionality simulated by the simulator)

   with an ideal functionality, there will be no corresponding
   simulator in the ideal world, but the base adversarial port index
   will be the one by which it communicates with the adversary *)

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
                       let num_adv_pis =
                         match unit_info_of_root maps (fst sp) with
                         | UI_Singleton _ -> failure "cannot happen"
                         | UI_Triple ti   -> ti.ti_num_adv_pis in
                       iter (rwas @ [RWA_Ideal (sp, base)]) (base + num_adv_pis)
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

(* making formulas *)

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

let make_port_form (addr : form) (pi : form) : form =
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

let uc_qsym_prefix_distr = ["Top"; "Distr"]

let support_op (ty : ty) : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_distr, "support")) [ty]
  (tfun (tdistr ty) (tfun ty tbool))

let support_form (ty : ty) (d : form) (x : form) : form =
  f_app (support_op ty) [d; x] tbool

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

let pp_global_context (ppf : formatter) (gc : global_context) : unit =
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
  fprintf ppf "@[(@[%a@])@]"
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

let gc_make_unique_id (gc : global_context) (id : symbol) : symbol =
  let rec find (n : int) : symbol =
    let next = id ^ BatInt.to_string n in
    if try ignore (EcEnv.LDecl.by_name next gc); true with
       | EcEnv.LDecl.LdeclError _ -> false
    then next
    else find (n + 1) in
  try ignore (EcEnv.LDecl.by_name id gc); id with
  | EcEnv.LDecl.LdeclError _ -> find 0

(* for handling random assignments

   it's up to the user to ensure the distribution has a nonempty
   support - otherwise the added hypothesis will introduce an
   inconsistency *)

let gc_add_rand (gc : global_context) (id_base : symbol) (hyp_base : symbol)
    (ty : ty)
    (dist : form)  (* should have type tdistr ty *)
      : global_context * EcIdent.t =
  let id = EcIdent.create (gc_make_unique_id gc id_base) in
  let hyp = EcIdent.create (gc_make_unique_id gc hyp_base) in
  let support_app = support_form ty dist (f_local id ty) in
  let gc = LDecl.add_local id (EcBaseLogic.LD_var (ty, None)) gc in
  let gc =  LDecl.add_local hyp (EcBaseLogic.LD_hyp support_app) gc in
  (gc, id)

(* a local context is a nonempty stack of maps (frames) from
   identifers (local variables or bound identifiers (state parameters
   or ones bound by message match clauses or ordinary match clauses))
   to formulas, which should be well typed in the global context

   the bottom frame is its first element, ..., and the top frame is
   its last element

   the bottom frame includes entries corresponding to local_context_base
   (see below); the remaining frames bind identifers bound by
   ordinary meatch clauses

   in practice, all the EcIdent.t's of all the frames will be
   distinct, because of their tags *)

type local_context_frame = form EcIdent.Mid.t
type local_context       = local_context_frame list

(* in an LCB_IntPort (id, f), the string of id will have the form
   "intport." followed the name of the party (which in the case of a
   simulator will consists of the (unqualified by the root) name of
   the real functionality being simulated, followed by '.', followed
   by the party) *)

type local_context_base =
  | LCB_Bound   of EcIdent.t * form  (* bound identifier - state param or
                                        of message match clause *)
  | LCB_Var     of EcIdent.t * ty    (* local variable *)
  | LCB_EnvPort of form * form       (* both of type address *)
  | LCB_IntPort of EcIdent.t * form  (* of type port *)

let lc_create (lcbs : local_context_base list) : local_context =
  [EcIdent.Mid.of_list
   (List.map
    (fun lcb ->
       match lcb with
       | LCB_Bound (id, form)    -> (id, form)
       | LCB_Var (id, ty)        ->
           (id, f_op EcCoreLib.CI_Witness.p_witness [ty] ty)
       | LCB_EnvPort (func, adv) ->
           (envport_id,
            f_app (form_of_expr mhr envport_op)
            [func; adv] (tfun port_ty tbool))
       | LCB_IntPort (id, port)  -> (id, port))
    lcbs)]

(* when we pretty print the identifier of an internal port entry,
   we replace the ':' by ' ', so it matches the concrete syntax *)

let pp_local_context (env : env) (ppf : formatter) (lc : local_context) : unit =
  let subst_colon_by_blank (s : symbol) : symbol =
    String.map (fun c -> if c = ':' then ' ' else c) s in
  let pp_frame_entry (ppf : formatter) ((id, form) : EcIdent.t * form)
        : unit =
    fprintf ppf "@[%s ->@ %a@]"
    (subst_colon_by_blank (EcIdent.name id))
    (pp_form env) form in
  let pp_frame (ppf : formatter) (frame : form EcIdent.Mid.t) : unit =
    fprintf ppf "@[(@[%a@])@]"
    (EcPrinting.pp_list ",@ " pp_frame_entry)
    (EcIdent.Mid.bindings frame) in
  let rec pp_frames (ppf : formatter) (frames : form EcIdent.Mid.t list)
        : unit =
    match frames with
    | []              -> failure "should not happen"
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

let push (lc : local_context) (fr : local_context_frame) : local_context =
  lc @ [fr]

let pop (lc : local_context) : local_context =
  (if List.is_empty lc then failure "should not happen");
  List.take (List.length lc - 1) lc

(* handle a random assignment *)

let gc_lc_random_assign (gc : global_context) (lc : local_context)
    (id_base : symbol) (hyp_base : symbol)
    (ty : ty)             (* type of variable *)
    (var_id : EcIdent.t)  (* variable - lhs of assignment, type ty *)
    (dist : form)         (* rhs of assignment, type tdistr ty *)
      : global_context * local_context *
        symbol =  (* name of id standing for sampled value *)
  let (gc, id) = gc_add_rand gc id_base hyp_base ty dist in
  let lc = lc_update_var lc var_id (f_local id ty) in
  (gc, lc, EcIdent.name id)

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
     pr_timelimit = 3}

(* Using EasyCrypt Proof Engine *)

exception ECProofEngine

let eval_bool_form_to_bool (gc : global_context) (pi : prover_infos)
    (f : form) : bool =
  let () =
    debugging_message
    (fun ppf ->
       fprintf ppf
       ("@[@[trying@ to@ prove@ truth@ or@ falsity@ " ^^
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
      raise ECProofEngine

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
  | RWRC_IdealFunc of int list  *
                      int       *  (* base adversarial port index *)
                      symb_pair *  (* functionality *)
                      symbol       (* state name *)
  | RWRC_RealFunc  of int list  *
                      int       *  (* base adversarial port index *)
                      symb_pair *  (* functionality *)
                      symbol    *  (* party name *)
                      symbol       (* state name *)

let pp_relative_address (ppf : formatter) (addr : int list) : unit =
  fprintf ppf "[@[%a@]]"
  (EcPrinting.pp_list ",@ " pp_int) addr

let pp_symb_pair (ppf : formatter) (sp : symb_pair) : unit =
  fprintf ppf "%s.%s" (fst sp) (snd sp)

let pp_rel_addr_ideal_func_info (ppf : formatter)
    ((is, sp_func) : int list * symb_pair) : unit =
  fprintf ppf "@[%a:@ %a@]"
  pp_relative_address is
  pp_symb_pair sp_func

let pp_rel_addr_real_func_info (ppf : formatter)
    ((is, sp_func, pty_id) : int list * symb_pair * symbol) : unit =
  fprintf ppf "@[%a:@ %a/%s@]"
  pp_relative_address is
  pp_symb_pair sp_func
  pty_id

(* no need to pretty-print adversarial port indices, as the
   user can look these up in real world *)

let pp_real_world_running_context (ppf : formatter)
    (rwrc : real_world_running_context) : unit =
  match rwrc with
  | RWRC_IdealFunc (is, _, sp_func, state_id)        ->
      fprintf ppf "@[running at %a:@ %a/@,%s@]"
      pp_relative_address is
      pp_symb_pair sp_func
      state_id
  | RWRC_RealFunc (is, _, sp_func, pty_id, state_id) ->
      fprintf ppf "@[running at %a:@ %a/@,%s/@,%s@]"
      pp_relative_address is
      pp_symb_pair sp_func
      pty_id state_id

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

let maps_of_config (conf : config) : maps_tyd =
  match conf with
  | ConfigGen c          -> c.maps
  | ConfigReal c         -> c.maps
  | ConfigIdeal c        -> c.maps
  | ConfigRealRunning c  -> c.maps
  | ConfigIdealRunning c -> c.maps
  | ConfigRealSending c  -> c.maps
  | ConfigIdealSending c -> c.maps

let gc_of_config (conf : config) : global_context =
  match conf with
  | ConfigGen c          -> c.gc
  | ConfigReal c         -> c.gc
  | ConfigIdeal c        -> c.gc
  | ConfigRealRunning c  -> c.gc
  | ConfigIdealRunning c -> c.gc
  | ConfigRealSending c  -> c.gc
  | ConfigIdealSending c -> c.gc

let prover_infos_of_config (conf : config) : prover_infos =
  match conf with
  | ConfigGen c          -> c.pi
  | ConfigReal c         -> c.pi
  | ConfigIdeal c        -> c.pi
  | ConfigRealRunning c  -> c.pi
  | ConfigIdealRunning c -> c.pi
  | ConfigRealSending c  -> c.pi
  | ConfigIdealSending c -> c.pi

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

let typecheck_and_pp_sent_msg_expr (conf : config) (sme : sent_msg_expr)
      : string =
  let env = env_of_config conf in
  let sme = inter_check_sent_msg_expr (maps_of_config conf) env sme in
  pp_sent_msg_expr_to_string env sme

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
  pp_global_context gc

let pp_local_context_msg (env : env) (ppf : formatter)
    (lc : local_context) : unit =
  fprintf ppf
  "@[local context:@ %a@]"
  (pp_local_context env) lc

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
      (pp_local_context_msg (env_of_gc c.gc)) c.lc
  | ConfigIdealRunning c ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n@\n%a@]"
      pp_global_context_msg c.gc
      (pp_ideal_world_with_states_msg c.maps c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_ideal_world_running_context c.iwrc
      (pp_local_context_msg (env_of_gc c.gc)) c.lc
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
  let pi = default_prover_infos (env_of_gc gc) in
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

let add_var_to_config_make_unique (conf : config) (id : psymbol)
    (pty : pty) : config * symbol =
  let l = loc id in
  let id = gc_make_unique_id (gc_of_config conf) (unloc id) in
  (add_var_to_config conf (mk_loc l id) pty, id)

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

let add_hyp_to_config_make_unique (conf : config) (id : psymbol)
    (pexpr : pexpr) : config * symbol =
  let l = loc id in
  let id = gc_make_unique_id (gc_of_config conf) (unloc id) in
  (add_hyp_to_config conf (mk_loc l id) pexpr, id)

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
  | EffectOK                          (* step succeeded (not random
                                         assignment), and new configuration
                                         is running or sending *)
  | EffectRand of symbol              (* step added ident representing
                                         random choice to global context,
                                         and new configuration is running *)
  | EffectMsgOut of string * control  (* a message was output, and new
                                         configuration is real or ideal;
                                         control says who has control *)
  | EffectFailOut                     (* fail was output, and new
                                         configuration is real or ideal *)
  | EffectBlockedIf                   (* configuration is running *)
  | EffectBlockedMatch                (* configuration is running *)
  | EffectBlockedPortOrAddrCompare    (* configuration is running or sending *)

let pp_effect (ppf : formatter) (e : effect) : unit =
  match e with
  | EffectOK                       -> fprintf ppf "EffectOK"
  | EffectRand id                  -> fprintf ppf "EffectRand: %s" id
  | EffectMsgOut (pp_sme, ctrl)    ->
      fprintf ppf "EffectMsgOut: %a: %s" pp_control ctrl pp_sme
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
      let pp_sme = pp_sent_msg_expr_to_string (env_of_gc c.gc) c.sme in
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; rw = c.rw; ig = c.ig; rws = c.rws;
        ctrl = ctrl},
       EffectMsgOut (pp_sme, ctrl))
  | ConfigIdealSending c ->
      let pp_sme = pp_sent_msg_expr_to_string (env_of_gc c.gc) c.sme in
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; iw = c.iw; ig = c.ig; iws = c.iws;
        ctrl = ctrl},
       EffectMsgOut (pp_sme, ctrl))
  | _                    -> raise ConfigError

let inter_check_sent_msg_expr_consistency
    (maps : maps_tyd) (gc : global_context)
    (pi : prover_infos) (sme : sent_msg_expr) : sent_msg_expr_tyd =
  let sme_ty = inter_check_sent_msg_expr maps (env_of_gc gc) sme in
  let check_consist (sme : sent_msg_expr_ord_tyd) (pi_form : form)
      (src_or_dest : string) (l : EcLocation.t) : unit =
    match sme.path.inter_id_path with
    | root :: comp :: [sub] ->
        (match unloc (Option.get (get_inter_tyd maps root comp)) with
         | BasicTyd _       -> failure "cannot happen"
         | CompositeTyd map ->
             let porti = id_map_ordinal1_of_sym map sub
             in if eval_bool_form_to_bool gc pi
                   (f_eq pi_form (int_form porti))
                then ()
                else error_message l
                     (fun ppf ->
                        fprintf ppf
                        ("@[%s@ port@ index@ is@ inconsistent@ with@ " ^^
                         "message@ path@]")
                        src_or_dest))
    | _ :: [bas]            ->
        if eval_bool_form_to_bool gc pi
           (f_eq pi_form (int_form 1))
        then ()
        else error_message l
             (fun ppf ->
                fprintf ppf
                ("@[%s@ port@ index@ is@ inconsistent@ with@ " ^^
                 "message@ path@]")
                src_or_dest)
    | _                     -> failure "cannot happen" in
  match sme_ty with
  | SMET_Ord sme_ty ->
      if sme_ty.dir = In
      then let dest_pi = port_to_pi_form sme_ty.out_port_form in
           check_consist sme_ty dest_pi "destination"
           (loc_of_out_of_sent_msg_expr sme);
           SMET_Ord sme_ty
      else let source_pi = port_to_pi_form sme_ty.in_port_form in
           check_consist sme_ty source_pi "source"
           (loc_of_in_of_sent_msg_expr sme);
           SMET_Ord sme_ty
  | sme_ty          -> sme_ty

let send_message_to_real_or_ideal_config
    (conf : config) (sme : sent_msg_expr) : config =
  match conf with
  | ConfigReal c  ->
      let sme =
        inter_check_sent_msg_expr_consistency c.maps c.gc c.pi sme in
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
      let sme =
        inter_check_sent_msg_expr_consistency c.maps c.gc c.pi sme in
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

let step_real_running_config (c : config_real_running) (pi : prover_infos)
      : config * effect =
  fill_in "step_real_running_config" (ConfigRealRunning c)

let step_ideal_running_config (c : config_ideal_running) (pi : prover_infos)
      : config * effect =
  fill_in "step_real_running_config" (ConfigIdealRunning c)

(* should only be called with ordinary sme that will successfully
   match *)

let match_ord_sme_against_msg_match_clauses
    (clauses : msg_match_clause_tyd list) (sme : sent_msg_expr_ord_tyd)
      : (EcIdent.t * form) list * instruction_tyd list located =
  let rec match_sme clauses =
    match clauses with
    | []                -> failure "should not happen"
    | clause :: clauses ->
        let {msg_pat; code} = clause in
        let {port_id; msg_path_pat; pat_args} = msg_pat in
        let {inter_id_path; msg_or_star} = unloc msg_path_pat in
        match msg_or_star with
        | MsgOrStarMsg msg ->
           if List.tl sme.path.inter_id_path = inter_id_path &&
              sme.path.msg = msg
           then (match_msg_pat msg_pat sme.in_port_form sme.args, code)
           else match_sme clauses
        | MsgOrStarStar    ->
            if UcUtils.sl1_starts_with_sl2 (List.tl sme.path.inter_id_path)
               inter_id_path
            then ([], code)  (* code will be fail *)
            else match_sme clauses in
  match_sme clauses

(* should only be called with ordinary sme that will successfully
   match *)

let match_ord_sme_in_state (rel_addr : int list) (sbt : state_body_tyd)
    (state_args : form list) (sme : sent_msg_expr_ord_tyd)
      : local_context * instruction_tyd list located =
  let addr = addr_concat_form func_form (addr_make_form rel_addr) in
  let port_of_addr i = make_port_form addr (int_form i) in
  let state_params =
    List.map (fun (id, f) -> (LCB_Bound (id, f)))
    (match_state_args sbt.params state_args) in
  let (mm_binds, mm_instructs) =
    match_ord_sme_against_msg_match_clauses sbt.mmclauses sme in
  let vars =
    List.map (fun (_, (id, ty)) -> LCB_Var (id, ty))
    (IdMap.bindings (unlocm sbt.vars)) in
  let mm_binds =
    List.map (fun (id, f) -> (LCB_Bound (id, f))) mm_binds in
  let envport = LCB_EnvPort (addr, adv_form) in
  let internal_ports =
    List.mapi
    (fun i (_, id) -> LCB_IntPort (id, port_of_addr (i + 1)))
    (QidMap.bindings sbt.internal_ports) in
  let lc =
    lc_create
    (state_params   @
     vars           @
     mm_binds       @
     [envport]      @
     internal_ports
    ) in
   (lc, mm_instructs)

let from_adv_to_func_find_rel_addr_adv_pi_func_sp
    (gc : global_context) (pi : prover_infos)
    (maps : maps_tyd) (dest_addr : form) (rw : real_world)
      : (int list * int * symb_pair) option =
  let try_sub_funs (sp : symb_pair) (rel : int list) (base : int)
      (nargs : int) : (int list * int * symb_pair) option =
    let ft = IdPairMap.find sp maps.fun_map in
    let num_sub_funs = num_sub_funs_of_real_fun_tyd ft in
    let rec try_sf (i : int) : (int list * int * symb_pair) option =
      let rel_nargs_i = rel @ [nargs + i] in
      if i > num_sub_funs
        then None
      else if eval_bool_form_to_bool gc pi
              (f_eq
               (addr_concat_form func_form
                (addr_make_form rel_nargs_i))
               dest_addr)
        then Some
             (rel_nargs_i,
              get_adv_pi_of_nth_sub_fun_of_real_fun maps
              (fst sp) nargs base ft (i - 1),
              sub_fun_sp_nth_of_real_fun_tyd ft (i - 1))
      else try_sf (i + 1) in
    try_sf 1 in

  let rec find ((sp, adv_pi, rwas) : real_world) (rel : int list)
        : (int list * int * symb_pair) option =
    if eval_bool_form_to_bool gc pi
       (f_eq (addr_concat_form func_form (addr_make_form rel)) dest_addr)
    then Some (rel, adv_pi, sp)
    else let nargs = List.length rwas in
         let rec loop_args i =
           if i > nargs
             then try_sub_funs sp rel adv_pi nargs
           else let rel_i = rel @ [i] in
                let addr_i =
                  addr_concat_form func_form (addr_make_form rel_i) in
                if eval_bool_form_to_bool gc pi
                   (addr_le_form addr_i dest_addr)
                then match List.nth rwas (i - 1) with
                     | RWA_Real rw            -> find rw (rel @ [i])
                     | RWA_Ideal (sp, adv_pi) ->
                         if eval_bool_form_to_bool gc pi
                            (f_eq addr_i dest_addr)
                         then Some (rel_i, adv_pi, sp)
                         else None
                else loop_args (i + 1) in
         loop_args 1
  in find rw []

type real_world_rel_select =
  | RW_Select_RealFun     of symb_pair * int * real_world_arg list *
                             (symb_pair *  (* if arg: parent *)
                              int *        (* index into parent's args *)
                              int) option  (* parent's adv pi *)
  | RW_Select_IdealFunArg of symb_pair * int *
                             symb_pair *   (* parent *)
                             int       *   (* index into parent's args *)
                             int           (* parent's adv pi *)
  | RW_Select_IdealSubFun of symb_pair * int *
                             symb_pair *   (* parent *)
                             int       *   (* index into parent's sub funs *)
                             int           (* parent's adv pi *)

let select_rel_addr_of_real_world
    (maps : maps_tyd) (rel : int list) (rw : real_world)
      : real_world_rel_select option =
  let rec sel (rel : int list) ((sp_par, base, rwas) : real_world)
      (par_opt : (symb_pair * int * int) option) =
    match rel with
    | []       -> Some (RW_Select_RealFun (sp_par, base, rwas, par_opt))
    | i :: rel ->  (* i starts at 1 *)
        let nargs = List.length rwas in
        if i <= 0
          then None
        else if i <= nargs
          then (match List.nth rwas (i - 1) with
                | RWA_Real rw           ->
                    sel rel rw (Some (sp_par, i - 1, base))
                | RWA_Ideal (sp, advpi) ->
                    Some
                    (RW_Select_IdealFunArg (sp, advpi, sp_par, i - 1, base)))
        else let ft = IdPairMap.find sp_par maps.fun_map in
             let num_sub_funs = num_sub_funs_of_real_fun_tyd ft in
             let j = i - num_sub_funs in
             if j <= num_sub_funs
             then Some
                  (RW_Select_IdealSubFun
                   (sub_fun_sp_nth_of_real_fun_tyd ft (j - 1),
                    get_adv_pi_of_nth_sub_fun_of_real_fun maps
                    (fst sp_par) nargs base ft (j - 1),
                   sp_par, j - 1, base))
             else None
  in sel rel rw None

let step_real_sending_config (c : config_real_sending) (pi : prover_infos)
      : config * effect =
  let mode = mode_of_sent_msg_expr_tyd c.sme in
  let dest_port = dest_port_of_sent_msg_expr_tyd c.sme in
  let dest_addr = port_to_addr_form dest_port in
  let dest_pi = port_to_pi_form dest_port in
  let source_port = source_port_of_sent_msg_expr_tyd c.sme in
  let source_addr = port_to_addr_form source_port in
  let source_pi = port_to_pi_form source_port in

  let from_env_to_func_find_party (rfi : real_fun_info)
        : (symbol * symbol * symbol) option =
    let rec find (bndgs : (symbol * party_info) list)
          : (symbol * symbol * symbol) option =
      match bndgs with
      | []                          -> None
      | (pty_id, pty_info) :: bndgs ->
          match pty_info.pi_pdi with
          | None                   -> find bndgs
          | Some (comp, sub, pind) ->
              if eval_bool_form_to_bool c.gc pi
                 (f_eq dest_pi (int_form pind))
              then Some (pty_id, comp, sub)
              else find bndgs
    in find (IdMap.bindings rfi) in

  let from_env_to_func_match (base : int) (func_sp : symb_pair)
      (party_id : symbol) (comp : symbol) (sub : symbol) (state_id : symbol)
      (state_args : form list) (sbt : state_body_tyd) : config * effect =
    match c.sme with
    | SMET_Ord sme_ord        ->
        let (root, func_id) = func_sp in
        let iip = sme_ord.path.inter_id_path in
        if List.hd iip = root && List.tl iip = [comp; sub] &&
           sme_ord.dir = In
        then let (lc, ins) =
               match_ord_sme_in_state [] sbt state_args sme_ord in
             (ConfigRealRunning
              {maps = c.maps;
               gc   = c.gc;
               pi   = c.pi;
               rw   = c.rw;
               ig   = c.ig;
               rws  = c.rws;
               rwrc = RWRC_RealFunc ([], base, func_sp, party_id, state_id);
               lc   = lc;
               ins  = create_instr_interp_list_loc ins},
              EffectOK)
        else (debugging_message
              (fun ppf ->
                 fprintf ppf
                 "@[message@ match@ failure@ at@ %a@]"
                 pp_rel_addr_real_func_info ([], func_sp, party_id));
              fail_out_of_running_or_sending_config (ConfigRealSending c))
    | SMET_EnvAdv sme_env_adv -> failure "cannot happen" in

  let from_env () =
    if mode = Dir &&
       eval_bool_form_to_bool c.gc pi
       (f_and
        (f_eq dest_addr func_form)
        (envport_form func_form adv_form source_port))
      then let (func_sp, base, _) = c.rw in
           let (root, fid) = func_sp in
           let ft = IdPairMap.find func_sp c.maps.fun_map in
           let rfi = get_info_of_real_func c.maps root base ft in
           match from_env_to_func_find_party rfi with
           | None                  ->
               (debugging_message
                (fun ppf ->
                   fprintf ppf
                   ("@[unable@ to@ find@ party@ accepting@ " ^^
                    "destination@ port@ id@]"));
               fail_out_of_running_or_sending_config (ConfigRealSending c))
           | Some (pid, comp, sub) ->
               let pbt = unloc (party_of_real_fun_tyd ft pid) in
               let rs = real_state_of_fun_state (ILMap.find [] c.rws) in
               let {id = state_id; args = state_args} = IdMap.find pid rs in
               let sbt = unloc (IdMap.find state_id pbt.states) in
               from_env_to_func_match base func_sp pid comp sub
               state_id state_args sbt
    else if mode = Adv &&
            eval_bool_form_to_bool c.gc pi
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

  let from_adv_to_func_find_party (rfi : real_fun_info)
        : (symbol * symbol * symbol) option =
    let rec find (bndgs : (symbol * party_info) list)
          : (symbol * symbol * symbol) option =
      match bndgs with
      | []                          -> None
      | (pty_id, pty_info) :: bndgs ->
          match pty_info.pi_pai with
          | None                           -> find bndgs
          | Some (comp, sub, pind, adv_pi) ->
              if eval_bool_form_to_bool c.gc pi
                 (f_and
                  (f_eq source_pi (int_form adv_pi))
                  (f_eq dest_pi (int_form pind)))
              then Some (pty_id, comp, sub)
              else find bndgs
    in find (IdMap.bindings rfi) in

  let from_adv_to_func_match (rel : int list) (base : int)
      (func_sp : symb_pair) (party_id : symbol)
      (comp : symbol) (sub : symbol) (state_id : symbol)
      (state_args : form list) (sbt : state_body_tyd) : config * effect =
    match c.sme with
    | SMET_Ord sme_ord        ->
        let (root, func_id) = func_sp in
        let iip = sme_ord.path.inter_id_path in
        if List.hd iip = root && List.tl iip = [comp; sub] &&
           sme_ord.dir = In
        then if sbt.is_initial
             then (debugging_message
                   (fun ppf ->
                      fprintf ppf
                      ("@[adversarial@ message@ rejected@ in@ initial@ " ^^
                       "state@ at@ %a@]")
                      pp_rel_addr_real_func_info (rel, func_sp, party_id));
                   fail_out_of_running_or_sending_config
                   (ConfigRealSending c))
             else let (lc, ins) =
                    match_ord_sme_in_state rel sbt state_args sme_ord in
                  (ConfigRealRunning
                   {maps = c.maps;
                    gc   = c.gc;
                    pi   = c.pi;
                    rw   = c.rw;
                    ig   = c.ig;
                    rws  = c.rws;
                    rwrc =
                      RWRC_RealFunc (rel, base, func_sp, party_id, state_id);
                    lc   = lc;
                    ins  = create_instr_interp_list_loc ins},
                   EffectOK)
        else (debugging_message
              (fun ppf ->
                 fprintf ppf
                 "@[message@ match@ failure@ at@ %a@]"
                 pp_rel_addr_real_func_info (rel, func_sp, party_id));
              fail_out_of_running_or_sending_config (ConfigRealSending c))
    | SMET_EnvAdv _    ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            "@[message@ match@ failure@ at@ %a@]"
            pp_rel_addr_ideal_func_info (rel, func_sp));
         fail_out_of_running_or_sending_config (ConfigRealSending c)) in

  let from_adv_to_real_func (rel : int list) (base : int)
      (func_sp : symb_pair) (rfbt : real_fun_body_tyd) : config * effect =
    let (root, fid) = func_sp in
    let ft = IdPairMap.find func_sp c.maps.fun_map in
    let rfi = get_info_of_real_func c.maps root base ft in
    match from_adv_to_func_find_party rfi with
    | None                  ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            ("@[unable@ to@ find@ party@ accepting@ " ^^
             "source@ and@ destination@ port@ ids@]"));
         fail_out_of_running_or_sending_config (ConfigRealSending c))
    | Some (ptyid, comp, sub) ->
        let pbt = unloc (party_of_real_fun_tyd ft ptyid) in
        let rs = real_state_of_fun_state (ILMap.find rel c.rws) in
        let {id = state_id; args = state_args} = IdMap.find ptyid rs in
        let sbt = unloc (IdMap.find state_id pbt.states) in
        from_adv_to_func_match rel base func_sp ptyid comp sub
        state_id state_args sbt in

  let from_adv_to_ideal_func (rel : int list) (adv_pi : int)
      (func_sp : symb_pair) (ifbt : ideal_fun_body_tyd) : config * effect =
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, func_id) = func_sp in
        let basic = ifbt.id_adv_inter in
        let {id = state_id; args = state_args} =
          ideal_state_of_fun_state (ILMap.find rel c.rws) in
        let sbt = unloc (IdMap.find state_id ifbt.states) in
        let iip = sme_ord.path.inter_id_path in
        if List.hd iip = root && List.tl iip = [basic] &&
           sme_ord.dir = In &&
           eval_bool_form_to_bool c.gc pi
           (f_and
            (f_eq source_pi (int_form adv_pi))
            (f_eq dest_pi   (int_form 1)))
        then if sbt.is_initial
             then (debugging_message
                   (fun ppf ->
                      fprintf ppf
                      ("@[adversarial@ message@ rejected@ in@ initial@ " ^^
                       "state@ at@ %a@]")
                      pp_rel_addr_ideal_func_info (rel, func_sp));
                   fail_out_of_running_or_sending_config
                   (ConfigRealSending c))
             else let (lc, ins) =
                    match_ord_sme_in_state rel sbt state_args sme_ord in
                  (ConfigRealRunning
                   {maps = c.maps;
                    gc   = c.gc;
                    pi   = c.pi;
                    rw   = c.rw;
                    ig   = c.ig;
                    rws  = c.rws;
                    rwrc = RWRC_IdealFunc ([], adv_pi, func_sp, state_id);
                    lc   = lc;
                    ins  = create_instr_interp_list_loc ins},
                   EffectOK)
        else (debugging_message
              (fun ppf ->
                 fprintf ppf
                 "@[message@ match@ failure@ at@ %a@]"
                 pp_rel_addr_ideal_func_info (rel, func_sp));
              fail_out_of_running_or_sending_config (ConfigRealSending c))
    | SMET_EnvAdv _    ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            "@[message@ match@ failure@ at@ %a@]"
            pp_rel_addr_ideal_func_info (rel, func_sp));
         fail_out_of_running_or_sending_config (ConfigRealSending c)) in

  let from_adv_to_func () : config * effect =
    match from_adv_to_func_find_rel_addr_adv_pi_func_sp
          c.gc pi c.maps dest_addr c.rw with
    | None                        ->
        fail_out_of_running_or_sending_config (ConfigRealSending c)
    | Some (rel, adv_pi, func_sp) ->
        let fbt = unloc (IdPairMap.find func_sp c.maps.fun_map) in
        match fbt with
        | FunBodyRealTyd rfbt  ->
            from_adv_to_real_func rel adv_pi func_sp rfbt
        | FunBodyIdealTyd ifbt ->
            from_adv_to_ideal_func rel adv_pi func_sp ifbt in

  let from_adv () =
    if mode = Dir ||
       eval_bool_form_to_bool c.gc pi
       (f_or
        (addr_le_form adv_form dest_addr)
        (f_or
         (f_not (f_eq adv_form source_addr))
         (int_lt_form source_pi (int_form 0))))
      then fail_out_of_running_or_sending_config (ConfigRealSending c)
    else if eval_bool_form_to_bool c.gc pi
            (addr_le_form func_form dest_addr)
      then if eval_bool_form_to_bool c.gc pi
              (f_eq source_pi (int_form 0))
           then fail_out_of_running_or_sending_config (ConfigRealSending c)
           else from_adv_to_func ()
    else if eval_bool_form_to_bool c.gc pi
            (f_iff
             (f_eq source_pi (int_form 0))
             (f_eq dest_port env_root_port_form))
      then msg_out_of_sending_config (ConfigRealSending c) CtrlEnv
    else fail_out_of_running_or_sending_config (ConfigRealSending c) in

  let from_parent_to_ideal_func (rel : int list) (adv_pi : int)
      (func_sp : symb_pair) (ifbt : ideal_fun_body_tyd) : config * effect =
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, func_id) = func_sp in
        let comp = ifbt.id_dir_inter in
        let comp_map =
          match unloc (IdPairMap.find (root, comp) c.maps.dir_inter_map) with
          | BasicTyd _ -> failure "cannot happen"
          | CompositeTyd map -> map in
        let {id = state_id; args = state_args} =
          ideal_state_of_fun_state (ILMap.find rel c.rws) in
        let sbt = unloc (IdMap.find state_id ifbt.states) in
        (match sme_ord.path.inter_id_path with
         | root' :: comp' :: [sub] ->
             if sme_ord.dir = In &&
                comp = comp' &&
                eval_bool_form_to_bool c.gc pi
                (f_eq dest_pi (int_form (id_map_ordinal1_of_sym comp_map sub)))
             then let (lc, ins) =
                    match_ord_sme_in_state rel sbt state_args sme_ord in
                  (ConfigRealRunning
                   {maps = c.maps;
                    gc   = c.gc;
                    pi   = c.pi;
                    rw   = c.rw;
                    ig   = c.ig;
                    rws  = c.rws;
                    rwrc = RWRC_IdealFunc (rel, adv_pi, func_sp, state_id);
                    lc   = lc;
                    ins  = create_instr_interp_list_loc ins},
                   EffectOK)
             else failure "should not happen"
         | _                       -> failure "should not happen")
    | SMET_EnvAdv _    ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            "@[message@ match@ failure@ at@ %a@]"
            pp_rel_addr_ideal_func_info (rel, func_sp));
         fail_out_of_running_or_sending_config (ConfigRealSending c)) in

  let from_parent_to_arg_or_sub_fun (rel : int list)
      (sp_par : symb_pair) (base : int) (rwas : real_world_arg list)
        : config * effect =
    let num_args = List.length rwas in
    let ft_par = IdPairMap.find sp_par c.maps.fun_map in
    let num_sub_funs = num_sub_funs_of_real_fun_tyd ft_par in
    let rec find_arg (i : int) : int option =
      if i > num_args
      then None
      else let rel_i = rel @ [i] in
           let addr_i =
             addr_concat_form func_form (addr_make_form rel_i) in
           if eval_bool_form_to_bool c.gc pi
              (f_eq dest_addr addr_i)
           then Some i
           else find_arg (i + 1) in
    let rec find_sub_fun (i : int) : int option =
      if i > num_sub_funs
      then None
      else let rel_i = rel @ [i] in
           let addr_i =
             addr_concat_form func_form (addr_make_form rel_i) in
           if eval_bool_form_to_bool c.gc pi
              (f_eq dest_addr addr_i)
           then Some i
           else find_sub_fun (i + 1) in
     match find_arg 1 with
     | None   ->
         (match find_sub_fun (num_args + 1) with
         | None   ->
             fail_out_of_running_or_sending_config (ConfigRealSending c)
         | Some i ->
             let sp = sub_fun_sp_nth_of_real_fun_tyd ft_par (i - 1) in
             let fbt = unloc (IdPairMap.find sp c.maps.fun_map) in
             let ifbt = ideal_fun_body_tyd_of fbt in
             from_parent_to_ideal_func (rel @ [i])
             (get_adv_pi_of_nth_sub_fun_of_real_fun c.maps
              (fst sp_par) num_args base ft_par (i - 1))
             sp ifbt)
     | Some i ->
         (match List.nth rwas (i - 1) with
          | RWA_Real (sp, adv_pi, _) ->
              failure "hi"
          | RWA_Ideal (sp, adv_pi)   ->
             let fbt = unloc (IdPairMap.find sp c.maps.fun_map) in
             let ifbt = ideal_fun_body_tyd_of fbt in
             from_parent_to_ideal_func (rel @ [i]) adv_pi sp ifbt) in

  let from_arg_or_sub_fun_to_parent (rel : int list)
      (rwrs : real_world_rel_select) : config * effect =
    match rwrs with
    | RW_Select_RealFun (sp, base, _, par_opt)                          ->
        (match par_opt with
         | None                               ->  (* to env *)
             msg_out_of_sending_config (ConfigRealSending c) CtrlEnv
         | Some (sp_par, par_arg_i, par_base) ->
             fill_in "message from func" (ConfigRealSending c))
    | RW_Select_IdealFunArg (sp, adv_pi, sp_par, par_arg_i, par_adv_pi) ->
        fill_in "message from func" (ConfigRealSending c)
    | RW_Select_IdealSubFun (sp, adv_pi, sp_par, par_arg_i, par_adv_pi) ->
        fill_in "message from func" (ConfigRealSending c) in

  let from_func (rel : int list) : config * effect =
    let rwrso = select_rel_addr_of_real_world c.maps rel c.rw in
    let cur_addr =
      addr_concat_form func_form (addr_make_form rel) in
    if mode = Adv
      then msg_out_of_sending_config (ConfigRealSending c) CtrlAdv
    else if eval_bool_form_to_bool c.gc pi
            (addr_lt_form cur_addr dest_addr)
      then (match BatOption.get rwrso with
            | RW_Select_RealFun (sp, base, rwas, _) ->
                from_parent_to_arg_or_sub_fun rel sp base rwas
            | _                                     ->
                fail_out_of_running_or_sending_config (ConfigRealSending c))
    else if eval_bool_form_to_bool c.gc pi
            (addr_lt_form dest_addr cur_addr)
      then from_arg_or_sub_fun_to_parent rel (BatOption.get rwrso)
    else failure "should not happen" in

  try
    match c.rwsc with
    | RWSC_Env                -> from_env ()
    | RWSC_Adv                -> from_adv ()
    | RWSC_FromFunc (rel, _) -> from_func rel
  with
  | ECProofEngine ->
      (ConfigRealSending c, EffectBlockedPortOrAddrCompare)

let step_ideal_sending_config (c : config_ideal_sending) (pi : prover_infos)
      : config * effect =
  fill_in "trying to step ideal sending config" (ConfigIdealSending c)

let step_running_or_sending_real_or_ideal_config
    (conf : config) (ppi_opt : EcParsetree.pprover_infos option)
      : config * effect =
  let pi =
    match ppi_opt with
    | None     -> prover_infos_of_config conf
    | Some ppi ->
        update_prover_infos (env_of_gc (gc_of_config conf))
        (prover_infos_of_config conf) ppi in
  match conf with
  | ConfigRealRunning c  -> step_real_running_config c pi
  | ConfigIdealRunning c -> step_ideal_running_config c pi
  | ConfigRealSending c  -> step_real_sending_config c pi
  | ConfigIdealSending c -> step_ideal_sending_config c pi
  | _                    -> raise ConfigError
