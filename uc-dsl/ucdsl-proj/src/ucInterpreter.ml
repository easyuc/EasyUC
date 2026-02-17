
(* UcInterpreter module *)

open Format

open EcSymbols
open EcLocation
open EcUtils
open EcAst
open EcParsetree
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
   its simulator in the ideal world (note that, except at the top level,
   this ideal functionality will be implicit - an argument of the
   application of the real functionality simulated by the simulator)

   with an ideal functionality, there will be no corresponding
   simulator in the ideal world, but the base adversarial port index
   will be the one by which it communicates with the adversary

   a real world / an ideal argument is tagged with the path of
   the theory in which interpretation will be done *)

type path = symbol list

type real_world = symb_pair * int * path * real_world_arg list

and real_world_arg =
  | RWA_Real  of real_world              (* a real functionality *)
  | RWA_Ideal of symb_pair * int * path  (* an ideal functionality *)

let adv_pi_of_rwa (rwa : real_world_arg) : int =
  match rwa with
  | RWA_Real (_, i, _, _) -> i
  | RWA_Ideal (_, i, _)   -> i

(* given a relative address, ns, of the destination port of a message,
   return Some of the symb_pair of the functionality to which that
   message is addressed, plus its adversarial port index (the base
   address of the given instance for a real or ideal functionality,
   and, in the case of a subfunctionality, the one that's calculated
   relative to the base adversarial port index of its real
   functionality), plus the path of the theory in which interpreation
   should happen; if ns is a bad relative address, return None *)

let rec select_real_world (maps : maps_tyd) (rw : real_world) (ns : int list)
      : (symb_pair * int * path) option =
  match ns with
  | []      ->
      let (sp, base, path, _) = rw in
      Some (sp, base, path)
  | n :: ns ->
      let (sp, base, path, rwas) = rw in
      if n < 1
        then None
      else if n <= List.length rwas
        then match List.nth rwas (n - 1) with
             | RWA_Real rw                -> select_real_world maps rw ns
             | RWA_Ideal (sp, base, path) ->
                 if List.is_empty ns
                 then Some (sp, base, path)
                 else None
      else if List.is_empty ns
        then let ft = IdPairMap.find sp maps.fun_map in
             let num_sub_funs = num_sub_funs_of_real_fun_tyd ft in
             let n = n - List.length rwas in
             if n <= num_sub_funs
             then let (root, id, clone) =
                    sub_fun_porsf_info_nth_of_real_fun_tyd ft (n - 1) in
                  Some
                  ((root, id),
                   get_adv_pi_of_nth_sub_fun_of_real_fun maps
                   (fst sp) base ft (n - 1),
                   path @ [clone])
             else None
      else None

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
   adversary); they are listed in the order of the parameters of the
   real functionality

   the ideal functionality and the simulators are all tagged with
   the path of the theory in which interpretation will be done *)

type ideal_world = {
  iw_ideal_func : symb_pair * int * path;
  iw_main_sim   : symb_pair * int * int list * path;
  iw_other_sims : (symb_pair * int * int list * path) list
}

type worlds = {
  worlds_real  : real_world;
  worlds_ideal : ideal_world
}

let pp_int (ppf : formatter) (i : int) : unit =
  fprintf ppf "%d" i

(* path will have length >= 2, and we omit the first two components,
   "Top" and the root *)

let pp_path (ppf : formatter) (path : path) : unit =
  fprintf ppf
  "%s" (UcUtils.string_of_id_path (List.drop 2 path))

let pp_paren_int_list sep (ppf : formatter) (is : int list) : unit =
  if List.is_empty is
  then ()
  else fprintf ppf "(@[%a@])"
       (EcPrinting.pp_list sep pp_int) is

let pp_world_fun_info (ppf : formatter) (sp, i, path : symb_pair * int * path)
      : unit =
  fprintf ppf
  "@[%s.%s[%a]:%i@]"
  (fst sp) (snd sp)
  pp_path path
  i

let pp_world_sim_info (ppf : formatter)
    (sp, i, is, path : symb_pair * int * int list * path) : unit =
  fprintf ppf
  "@[%s.%s[%a]:%i%a@]"
  (fst sp) (snd sp)
  pp_path path
  i
  (pp_paren_int_list ", ") is

let pp_worlds (ppf : formatter) (w : worlds) : unit =
  let rec pp_real_world (ppf : formatter) (rw : real_world) : unit =
    let sp, i, path, rwas = rw in
    match rwas with
    | [] ->
      fprintf ppf "@[%a@]"
      pp_world_fun_info (sp, i, path)
    | _  ->
      fprintf ppf "@[%a@,(@[%a@])@]"
      pp_world_fun_info (sp, i, path)
      (EcPrinting.pp_list ",@ " pp_real_world_arg) rwas

  and pp_real_world_arg (ppf : formatter) (rwa : real_world_arg)
        : unit =
    match rwa with
    | RWA_Real rw             -> fprintf ppf "%a" pp_real_world rw
    | RWA_Ideal (sp, i, path) ->
        fprintf ppf "%a" pp_world_fun_info (sp, i, path) in

  let rec pp_sims (ppf : formatter)
          (sims : (symb_pair * int * int list * path) list) : unit =
    match sims with
    | []        -> ()
    | [sim]     ->
      fprintf ppf " *@ %a"
      pp_world_sim_info sim
    | sim :: sims ->
      fprintf ppf " *@ %a%a"
      pp_world_sim_info sim
      pp_sims sims in

  let pp_ideal_world (ppf : formatter) (iw : ideal_world) : unit =
    fprintf ppf "@[%a /@ @[%a%a@]@]"
    pp_world_fun_info iw.iw_ideal_func
    pp_world_sim_info iw.iw_main_sim
    pp_sims iw.iw_other_sims in

  fprintf ppf "@[%a ~@ %a@]@."
  pp_real_world w.worlds_real
  pp_ideal_world w.worlds_ideal

(* the returned int is the first adversarial port index *not* used
   by the worlds *)

let fun_expr_tyd_to_worlds (maps : maps_tyd) (fet : fun_expr_tyd)
      : worlds * int =
  let rec fun_expr_to_worlds_base (fet : fun_expr_tyd) (base : int)
        : worlds * int =
    match fet with
    | FunExprTydReal ((root, fun_id), path, fets) ->
        (match unit_info_of_root maps root with
         | UI_Singleton _ -> failure "cannot happen"
         | UI_Triple ti   ->
             let rec iter
                 (rwas : real_world_arg list) (base : int)
                 (sims : (symb_pair * int * int list * path) list)
                 (fets : fun_expr_tyd list)
                   : real_world_arg list * int *
                     (symb_pair * int * int list * path) list =
               match fets with
               | []          -> (rwas, base, sims)
               | fet :: fets ->
                   match fet with
                   | FunExprTydReal _            ->
                       let (worlds, base) = fun_expr_to_worlds_base fet base in
                       iter (rwas @ [RWA_Real worlds.worlds_real]) base
                       (worlds.worlds_ideal.iw_main_sim ::
                        worlds.worlds_ideal.iw_other_sims @
                        sims)
                       fets
                   | FunExprTydIdeal (sp, path') ->
                       let num_adv_pis =
                         match unit_info_of_root maps (fst sp) with
                         | UI_Singleton _ -> failure "cannot happen"
                         | UI_Triple ti   -> ti.ti_num_adv_pis in
                       iter (rwas @ [RWA_Ideal (sp, base, path')])
                       (base + num_adv_pis) sims fets in
             let base' = base + ti.ti_num_adv_pis in
             let (rwas, base', sims) = iter [] base' [] fets in
             ({worlds_real  = ((root, fun_id), base, path, rwas);
               worlds_ideal =
                 {iw_ideal_func = ((root, ti.ti_ideal), base, path);
                  iw_main_sim   =
                    ((root, ti.ti_sim), base,
                     List.map adv_pi_of_rwa rwas, path);
                  iw_other_sims = sims}},
              base'))
     | FunExprTydIdeal _                          ->
         failure "should not be called with ideal functionality expression" in
  fun_expr_to_worlds_base fet 1

(* like UcTypedSpec.instruction_tyd and UcTypedSpec.instruction_tyd_u,
   but includes Pop instruction for popping a frame of local context

   we didn't need the location information for lists of instructions
   or clauses *)

type instr_interp_u =
  | Assign            of lhs * form
  | Sample            of lhs * form
  | ITE               of form * instr_interp list * instr_interp list option
  | Match             of form * match_clause_interp list
  | SendAndTransition of send_and_transition_tyd
  | Fail
  | Pop  (* pop frame of local context *)

and instr_interp = instr_interp_u located

and match_clause_interp = symbol * (bindings * instr_interp list)

let rec create_instr_interp (it : instruction_tyd) : instr_interp =
  mk_loc (loc it) (create_instr_interp_u (unloc it))

and create_instr_interp_list (its : instruction_tyd list located)
      : instr_interp list =
  List.map create_instr_interp (unloc its)

and create_instr_interp_u (itu : instruction_tyd_u) : instr_interp_u =
  match itu with
  | UcTypedSpec.Assign (lhs, exp)     -> Assign (lhs, exp)
  | UcTypedSpec.Sample (lhs, exp)     -> Sample (lhs, exp)
  | UcTypedSpec.ITE (exp, tins, eins) ->
      ITE
      (exp,
       create_instr_interp_list tins,
       omap create_instr_interp_list eins)
  | UcTypedSpec.Match (exp, clauses)  ->
      Match (exp, List.map create_match_clause_interp (unloc clauses))
  | UcTypedSpec.SendAndTransition sat -> SendAndTransition sat
  | UcTypedSpec.Fail                  -> Fail

and create_match_clause_interp ((sym, (bndgs, ins)) : match_clause_tyd)
      : match_clause_interp =
  (sym, (bndgs, create_instr_interp_list ins))

(* making formulas *)

let env_root_addr_form : form = env_root_addr_op

let env_root_port_form : form = env_root_port_op

let adv_addr_form : form = adv_addr_op

let envport_form (func : form) (pt : form) : form =
  f_app envport_op [func; pt] tbool

let inc_form (addr1 : form) (addr2 : form) : form =
  f_app inc_op [addr1; addr2] tbool

let addr_le_form (addr1 : form) (addr2 : form) : form =
  f_app addr_le_op [addr1; addr2] tbool

let addr_lt_form (addr1 : form) (addr2 : form) : form =
  f_app addr_lt_op [addr1; addr2] tbool

let addr_concat_form (addr1 : form) (addr2 : form) : form =
  f_app addr_concat_op [addr1; addr2] addr_ty

let addr_nil_form : form = addr_nil_op

let addr_cons_form (n : form) (addr : form) : form =
  f_app addr_cons_op [n; addr] addr_ty

let addr_make_form (ms : int list) : form =
  List.fold_right
  (fun m exp -> addr_cons_form (f_int (EcBigInt.of_int m)) exp)
  ms addr_nil_form

let addr_concat_form_from_list_smart (addr : form) (ms : int list) : form =
  if List.is_empty ms
  then addr
  else addr_concat_form addr (addr_make_form ms)

let port_to_addr_form (port : form) : form =
  f_proj port 0 addr_ty

let port_to_pi_form (port : form) : form =
  f_proj port 1 tint

let make_port_form (addr : form) (pi : form) : form =
  f_tuple [addr; pi]

let int_form (n : int) : form = f_int (EcBigInt.of_int n)

let int_add_form (n1 : form) (n2 : form) : form =
  f_app int_add_op [n1; n2] tint

let int_lt_form (n1 : form) (n2 : form) : form =
  f_app int_lt_op [n1; n2] tbool

let int_le_form (n1 : form) (n2 : form) : form =
  f_app int_le_op [n1; n2] tbool

let uc_qsym_prefix_distr = ["Top"; "Distr"]

let support_op (ty : ty) : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_distr, "support")) [ty]
  (tfun (tdistr ty) (tfun ty tbool))

let support_form (ty : ty) (d : form) (x : form) : form =
  f_app (support_op ty) [d; x] tbool

(* a global context is an EcEnv.LDecl.hyps *)

type global_context = LDecl.hyps

let func_id         : EcIdent.t = EcIdent.create "func"
let inc_func_adv_id : EcIdent.t = EcIdent.create "IncFuncAdv"

let func_form : form = f_local func_id addr_ty

(* test whether func_form is *abstract* in the sense that it doesn't
   appear freely in any assumptions (hypotheses) of a global context
   except inc_func_adv_id and applications of envport_op

   we say that func_form is *concrete* in gc iff it is not abstract in
   gc

   this is a sufficient (but not necessary) condition for knowing that
   func_form won't further simplify *)

let func_is_abstract_in_gc (gc : global_context) : bool =
  let is_abs_in_local (id, lk) =
    EcIdent.id_equal id inc_func_adv_id ||
    match lk with
    | EcBaseLogic.LD_hyp f ->
        not (Mid.mem func_id (f_fv f)) ||
        (match f.f_node with
         | Fapp (g, _) -> f_equal g envport_op
         | _           -> false)
    | _                    -> true
  in List.for_all is_abs_in_local (LDecl.tohyps gc).h_local

let gc_create (env : env) : global_context =
  let locs =
    [
      (func_id, EcBaseLogic.LD_var (addr_ty, None));
      (inc_func_adv_id,
       EcBaseLogic.LD_hyp
       (f_app inc_op [f_local func_id addr_ty; adv_addr_op]
        tbool))
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
         let ty = inter_check_type env pty in
         LDecl.add_local (EcIdent.create id)
         (EcBaseLogic.LD_var (ty, None)) gc
       with
       | EcTyping.TyError (l, env, tyerr) ->
           error_message l
           (fun ppf -> EcUserMessages.TypingError.pp_tyerror env ppf tyerr)

let gc_add_hyp (gc : global_context) (id : psymbol) (pform : pformula)
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
         let (form, _) = inter_check_expr env pform (Some tbool) in
         let gc =
           LDecl.add_local (EcIdent.create id)
           (EcBaseLogic.LD_hyp form) gc in
         let () =
           if not (func_is_abstract_in_gc gc)
           then debugging_message
                (fun ppf ->
                   fprintf ppf
                   ("@[func@ is@ now@ concrete,@ which@ may@ slow @ " ^^
                    "down@ interpretation@]"))
           else () in
         gc
       with
       | EcTyping.TyError (l, env, tyerr) ->
           error_message l
           (fun ppf -> EcUserMessages.TypingError.pp_tyerror env ppf tyerr)

let gc_make_unique_id (gc : global_context) (id : symbol) : symbol =
  let rec find (n : int) : symbol =
    let next = id ^ BatInt.to_string n in
    if try ignore (EcEnv.LDecl.by_name next gc); false with
     | EcEnv.LDecl.LdeclError _ -> true
    then next
    else find (n + 1) in
  if try ignore (EcEnv.LDecl.by_name id gc); false with
     | EcEnv.LDecl.LdeclError _ -> true
  then id
  else find 1

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
  let gc = LDecl.add_local hyp (EcBaseLogic.LD_hyp support_app) gc in
  (gc, id)

(* destruction of canonical ports to elements of the type
   canonical_port

   a port is *canonical* iff it has one of the following values of
   type form, where xs is a constant list of integers, and i is a
   constant integer

   see the code below for how these are actually represented as
   formulas

   ([], 0) or env_root_port_op

     destructs to CP_Root

   (adv_addr_op, i) or ([0], i)

     destructs to CP_Adv i

   adv_root_port_op (defined to be (adv_addr_op, 0))

     destructs to CP_Adv 0

   (func_id ++ xs, i)

     destructs to CP_FuncRel (xs, i) *)

type canonical_port =
   | CP_EnvRoot
   | CP_Adv     of int            (* the adversarial port index *)
   | CP_FuncRel of int list * int (* relative address plus port index *)

let destr_err() = raise (DestrError "can't destruct address or port")

let is_concat_op_path (path : EcPath.path) : bool =
  EcPath.p_equal path (EcPath.fromqsymbol (ec_qsym_prefix_list, "++"))

let is_concat_op (f : form) : bool =
  try let (path, _) = destr_op f in is_concat_op_path path
  with DestrError _ -> false

let is_cons_op_path (path : EcPath.path) : bool =
  EcPath.p_equal path
  (EcPath.fromqsymbol (ec_qsym_prefix_list, EcCoreLib.s_cons))

let is_cons_op (f : form) : bool =
  try let (path, _) = destr_op f in is_cons_op_path path
  with DestrError _ -> false

let is_nil_op_path (path : EcPath.path) : bool =
  EcPath.p_equal path
  (EcPath.fromqsymbol (ec_qsym_prefix_list, EcCoreLib.s_nil))

let is_nil_op (f : form) : bool =
  try let (path, _) = destr_op f in is_nil_op_path path
  with DestrError _ -> false

let is_func_id (f : form) : bool =
  try let id = destr_local f in EcIdent.id_equal id func_id
  with DestrError _ -> false

let is_env_root_port_op_path (path : EcPath.path) : bool =
  EcPath.p_equal path
  (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "env_root_port"))

let is_env_root_port_op (f : form) : bool =
  try let (path, _) = destr_op f in is_env_root_port_op_path path
  with DestrError _ -> false

let is_adv_op_path (path : EcPath.path) : bool =
  EcPath.p_equal path
  (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "adv"))

let is_adv_op (f : form) : bool =
  try let (path, _) = destr_op f in is_adv_op_path path
  with DestrError _ -> false

let is_adv_root_port_op_path (path : EcPath.path) : bool =
  EcPath.p_equal path
  (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "adv_root_port"))

let is_adv_root_port_op (f : form) : bool =
  try let (path, _) = destr_op f in is_adv_root_port_op_path path
  with DestrError _ -> false

(* the following functions can raise DestrError *)

let destr_int (f : form) : int =
  EcBigInt.to_int (destr_int f)

let rec destr_int_list f : int list =
  if is_nil_op f
  then []
  else match destr_app f with
       | (x, [y; z]) ->
           if is_cons_op x
           then destr_int y :: destr_int_list z
           else destr_err ()
       | _           -> destr_err ()

let destr_func_addr (addr : form) : int list =
  if is_func_id addr
  then []
  else match destr_app addr with
       | (x, [y; z]) ->
           if not (is_concat_op x)
             then destr_err ()
           else if (is_func_id y)
             then destr_int_list z
           else destr_err ()
       | _           -> destr_err ()

(* end of exception raising functions *)

let is_int (f : form) : bool =
  try let _ = destr_int f in true with
  | DestrError _ -> false

let is_int_non_opp (f : form) : bool =
  match f.f_node with
  | Fint _ -> true
  | _      -> false

let is_int_list (f : form) : bool =
  try let _ = destr_int_list f in true with
  | DestrError _ -> false

let is_adv_op_or_value (f : form) : bool =
  is_adv_op f ||
  try destr_int_list f = [0] with
  | DestrError _ -> false

let try_destr_port (port : form) : canonical_port option =
  try
    Some
    (if is_env_root_port_op port
       then CP_EnvRoot
     else if is_adv_root_port_op port
       then CP_Adv 0
     else match destr_tuple port with
          | [x; y] ->
              if is_adv_op_or_value x
                then CP_Adv (destr_int y)
              else if is_nil_op x
                then let n = destr_int y
                     in if n = 0 then CP_EnvRoot else destr_err ()
              else CP_FuncRel (destr_func_addr x, destr_int y)
          | _      -> destr_err ())
  with DestrError _ -> None

let is_canon_port (port : form) : bool =
  is_some (try_destr_port port)

let try_destr_port_as_port_index (port : form) : int option =
  match try_destr_port port with
  | None                   -> None
  | Some CP_EnvRoot        -> Some 0
  | Some CP_Adv i          -> Some i
  | Some CP_FuncRel (_, i) -> Some i

let try_destr_port_as_adv (port : form) : int option =
  match try_destr_port port with
  | Some CP_Adv i -> Some i
  | _             -> None

let try_destr_port_as_func_rel (port : form) : (int list * int) option =
  match try_destr_port port with
  | Some CP_FuncRel (rel, i) -> Some (rel, i)
  | _                        -> None

(* for debugging *)

let pp_canonical_port (ppf : formatter) (cp : canonical_port) : unit =
  match cp with
  | CP_EnvRoot         -> fprintf ppf "@[env root@]"
  | CP_Adv i           -> fprintf ppf "@[adv:@ %d@]" i
  | CP_FuncRel (xs, i) ->
      fprintf ppf
      "@[func@ rel:@ (@[[@[%a@]],@ %d@])@]"
      (EcPrinting.pp_list ";@ " pp_int) xs i

(* it's useful to have a notion of being *weakly simplified* that is
   strong enough for values (like arguments to messages and states)
   that we won't *immediately* need to make decisions about

   we start with values made out of true, false, the element of type
   unit, constructors and integer literals, but then we also allow leaves
   (not lhs's of applications) that are:

   * identifiers in the global context, even though they might be
     rewritten by assumptions

   * of the form (func ++ <int list literal>), but just when func is
     abstract *)

let is_weakly_simplified (env : env) (func_abstract : bool)
    (f : form) : bool =
  let rec is_weak_simp f =
    match f.f_node with
    | Fint _       -> true
    | Flocal _     -> true
    | Fop (op, _)  ->
        EcPath.p_equal op EcCoreLib.CI_Unit.p_tt    ||
        EcPath.p_equal op EcCoreLib.CI_Bool.p_true  ||
        EcPath.p_equal op EcCoreLib.CI_Bool.p_false ||
        Op.is_dtype_ctor env op
    | Fapp (f, fs) ->
        (match f.f_node with
         | Fop (op, _) ->
             if Op.is_dtype_ctor env op
               then List.for_all is_weak_simp fs
             else if f_equal f fop_int_opp  (* int negation *)
               then (match fs with
                     | [g] -> is_int_non_opp g
                     | _   -> false)
             else if is_concat_op_path op && func_abstract
               then (match fs with
                     | [fs1; fs2] -> is_func_id fs1 && is_int_list fs2
                     | _          -> false)
             else false
         | _           -> false)
    | Ftuple fs    -> List.for_all is_weak_simp fs
    | _            -> false
  in is_weak_simp f

(* prover infos *)

type prover_infos = EcProvers.prover_infos

let default_prover_infos () : prover_infos =
  {EcProvers.dft_prover_infos with
     pr_provers =
       List.filter EcProvers.is_prover_known
       EcProvers.dft_prover_names;
     pr_timelimit = 1}

let update_prover_infos (env : EcEnv.env) (pi : prover_infos)
    (ppi : EcParsetree.pprover_infos) : prover_infos =
  try EcScope.Prover.pprover_infos_to_prover_infos env pi ppi with
  | EcScope.HiScopeError (lopt, s) ->
      opt_loc_error_message lopt
      (fun ppf -> fprintf ppf "@[prover infos error: %s@]" s)

(* rewriting databases *)

type rewriting_dbs = qsymbol list

let pp_rewriting_dbs (ppf : Format.formatter) (dbs : rewriting_dbs) : unit =
  fprintf ppf "@[%a@]" (EcPrinting.pp_list ";@ " pp_qsymbol) dbs

let default_rewriting_dbs = [
  (["Top"; "UCBasicTypes"], "ucdsl_interpreter_hints")
]

let add_rewriting_db (env : env) (dbs : rewriting_dbs) (pdb : pqsymbol)
      : rewriting_dbs =
  let (db, l) = (unloc pdb, loc pdb) in
  match EcEnv.BaseRw.lookup_opt db env with
  | None   ->
      error_message l
      (fun ppf     ->
         fprintf ppf "@[bad@ rewriting@ database@]")
  | Some (path, _) ->
      let qsym = EcPath.toqsymbol path in
      if List.mem qsym dbs
      then error_message l
           (fun ppf ->
              fprintf ppf "@[already@ a@ rewriting@ database@]")
      else dbs @ [qsym]

let add_rewriting_dbs (env : env) (dbs : rewriting_dbs) (pdbs : pqsymbol list)
      : rewriting_dbs =
  List.fold_left
  (fun acc pdb -> add_rewriting_db env acc pdb)
  dbs pdbs

let rm_rewriting_db (env : env) (dbs : rewriting_dbs) (pdb : pqsymbol)
      : rewriting_dbs =
  let (db, l) = (unloc pdb, loc pdb) in
  let db_qual =
    match EcEnv.BaseRw.lookup_opt db env with
    | None           -> failure "cannot happen"
    | Some (path, _) -> EcPath.toqsymbol path in
  try let (i, _) = List.findi (fun _ x -> x = db_qual) dbs in
      List.remove_at i dbs with
  | Not_found ->
      error_message l
      (fun ppf ->
         fprintf ppf "@[not@ a@ current@ rewriting@ database@]")

let rm_rewriting_dbs (env : env) (dbs : rewriting_dbs) (pdbs : pqsymbol list)
      : rewriting_dbs =
  List.fold_left
  (fun acc pdb -> rm_rewriting_db env acc pdb)
  dbs pdbs

let modify_rewriting_dbs (env : env) (dbs : rewriting_dbs)
    (mod_dbs : mod_dbs) : rewriting_dbs =
  let dbs = rm_rewriting_dbs env dbs (fst mod_dbs) in
  add_rewriting_dbs env dbs (snd mod_dbs)

let lemmas_of_rewriting_dbs (env : env) (dbs : rewriting_dbs)
      : EcPath.path list =
  let lemmas_of_rw_dbs (db : qsymbol) : EcPath.path list =
    let lems = snd (EcEnv.BaseRw.lookup db env) in
    EcPath.Sp.elements lems in
  List.fold_left
  (fun acc db -> acc @ lemmas_of_rw_dbs db)
  [] dbs

(* using EasyCrypt proof engine *)

exception ECProofEngine

let eval_bool_form_to_bool (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (f : form) : bool =
  let () =
    debugging_message
    (fun ppf ->
       fprintf ppf
       ("@[@[trying@ to@ prove@ truth@ or@ falsity@ " ^^
        "of:@]@\n@[%a@]@]")
       (pp_form (env_of_gc gc)) f) in
  let rw_lems = lemmas_of_rewriting_dbs (env_of_gc gc) dbs in
  match UcEcFormEval.eval_condition gc f pi rw_lems with
  | UcEcFormEval.Bool b    ->
      (if b
       then debugging_message
            (fun ppf -> fprintf ppf "@[formula@ proved@]")
       else debugging_message
            (fun ppf -> fprintf ppf "@[formula's@ negation@ proved@]"));
      b
  | UcEcFormEval.Undecided ->
      (debugging_message
       (fun ppf ->
          fprintf ppf "@[unable@ to@ prove@ formula@ or@ its@ negation@]"));
      raise ECProofEngine

let simplify_formula (strong : bool) (gc : global_context)
    (dbs : rewriting_dbs) (f : form) : form =
  if not strong &&
     is_weakly_simplified (env_of_gc gc) (func_is_abstract_in_gc gc) f
  then f
  else let () =
         debugging_message
         (fun ppf ->
            fprintf ppf
            "@[@[trying@ to@ simplify@ formula:@]@\n@[%a@]@]"
            (pp_form (env_of_gc gc)) f) in
       let rw_lems = lemmas_of_rewriting_dbs (env_of_gc gc) dbs in
       let f = UcEcFormEval.simplify_formula gc f rw_lems in
       let () =
         debugging_message
         (fun ppf ->
            fprintf ppf
            "@[@[result@ is:@]@\n@[%a@]@]"
            (pp_form (env_of_gc gc)) f) in
       f

let simplify_port (gc : global_context) (dbs : rewriting_dbs)
      : form -> form =
  if func_is_abstract_in_gc gc
  then (fun (port : form) ->
          if is_canon_port port
          then port
          else simplify_formula true gc dbs port)
  else (fun (port : form) -> simplify_formula true gc dbs port)

let deconstruct_datatype_value (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (f : form) : symbol * EcCoreFol.form list =
  let () =
    debugging_message
    (fun ppf ->
       fprintf ppf
       "@[@[trying@ to@ deconstruct@ formula:@]@\n@[%a@]@]"
       (pp_form (env_of_gc gc)) f) in
  let f = simplify_formula true gc dbs f in
  let rw_lems = lemmas_of_rewriting_dbs (env_of_gc gc) dbs in
  let (constr, forms) : symbol * form list =
    try UcEcFormEval.deconstruct_data gc f pi rw_lems with
    | e when e <> Sys.Break ->
        (debugging_message
         (fun ppf -> fprintf ppf "@[deconstruction@ failed@]");
         raise ECProofEngine) in
  let () =
    debugging_message
    (fun ppf ->
       fprintf ppf
       ("@[@[result@ is:@]@\n@[@[constructor:@ %s@];@ " ^^
        "@[args:@ [@[%a@]]@]@]")
       constr
       (EcPrinting.pp_list ";@ " (pp_form (env_of_gc gc))) forms) in
  (constr, forms)

(* facilitating message routing, exploiting canonical ports when
   possible, but falling back on proof engine

   in the interpreter, we are not "baking in" the definition of envport,
   and so we will rely on simplification (or failing that SMT) for
   this; this is to allow for a possible restriction of envport in
   the future

   we *are* baking in that the addresses of the functionality and
   adversary are incomparable, and so are greater than the address
   of the root of the environment, which is [] *)

let equal_env_root_port (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (port : form) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs (f_eq port env_root_port_form)
  | Some CP_EnvRoot          -> true
  | Some _                   -> false

let equal_port_index_of_port (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (port : form) (i : int) : bool =
  match try_destr_port_as_port_index port with
  | None       ->
      eval_bool_form_to_bool gc pi dbs
      (f_eq (port_to_pi_form port) (int_form i))
  | Some porti -> porti = i

let less_than_port_index_of_port (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (port : form) (i : int) : bool =
  match try_destr_port_as_port_index port with
  | None       ->
      eval_bool_form_to_bool gc pi dbs
      (int_lt_form (port_to_pi_form port) (int_form i))
  | Some porti -> porti < i

let less_than_or_equal_port_index_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form) (i : int) : bool =
  match try_destr_port_as_port_index port with
  | None       ->
      eval_bool_form_to_bool gc pi dbs
      (int_le_form (port_to_pi_form port) (int_form i))
  | Some porti -> porti <= i

let greater_than_port_index_of_port (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (port : form) (i : int) : bool =
  match try_destr_port_as_port_index port with
  | None       ->
      eval_bool_form_to_bool gc pi dbs
      (int_lt_form (int_form i) (port_to_pi_form port))
  | Some porti -> porti > i

let greater_than_or_equal_port_index_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form) (i : int) : bool =
  match try_destr_port_as_port_index port with
  | None       ->
      eval_bool_form_to_bool gc pi dbs
      (int_le_form (int_form i) (port_to_pi_form port))
  | Some porti -> porti >= i

let equal_func_rel_addr_of_port (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (port : form) (xs : int list) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (f_eq (port_to_addr_form port)
       (addr_concat_form_from_list_smart func_form xs))
  | Some CP_FuncRel (rel, _) -> rel = xs
  | Some _                   -> false

let rec list_po_le (xs : int list) (ys : int list) : bool =
  match (xs, ys) with
  | ([],      _)       -> true
  | (_,       [])      -> false
  | (x :: xs, y :: ys) -> x = y && list_po_le xs ys

let rec list_po_lt (xs : int list) (ys : int list) : bool =
  match (xs, ys) with
  | ([],      [])      -> false
  | ([],      _)       -> true
  | (_,       [])      -> false
  | (x :: xs, y :: ys) -> x = y && list_po_lt xs ys

let less_than_func_rel_addr_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form)
    (xs : int list) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (addr_lt_form (port_to_addr_form port)
       (addr_concat_form_from_list_smart func_form xs))
  | Some CP_EnvRoot          -> true
  | Some CP_Adv _            -> false
  | Some CP_FuncRel (rel, _) -> list_po_lt rel xs

let less_than_or_equal_func_rel_addr_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form)
    (xs : int list) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (addr_le_form (port_to_addr_form port)
       (addr_concat_form_from_list_smart func_form xs))
  | Some CP_EnvRoot          -> true
  | Some CP_Adv _            -> false
  | Some CP_FuncRel (rel, _) -> list_po_le rel xs

let greater_than_func_rel_addr_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form)
    (xs : int list) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (addr_lt_form
       (addr_concat_form_from_list_smart func_form xs)
       (port_to_addr_form port))
  | Some CP_FuncRel (rel, _) -> list_po_lt xs rel
  | Some _                   -> false

let greater_than_or_equal_func_rel_addr_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form)
    (xs : int list) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (addr_le_form
       (addr_concat_form_from_list_smart func_form xs)
       (port_to_addr_form port))
  | Some CP_FuncRel (rel, _) -> list_po_le xs rel
  | Some _                   -> false

let equal_adv_addr_of_port (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (port : form) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (f_eq (port_to_addr_form port) adv_addr_form)
  | Some CP_Adv _            -> true
  | Some _                   -> false

let greater_than_or_equal_adv_addr_of_port (gc : global_context)
    (pi : prover_infos) (dbs : rewriting_dbs) (port : form) : bool =
  match try_destr_port port with
  | None                     ->
      eval_bool_form_to_bool gc pi dbs
      (addr_le_form adv_addr_form (port_to_addr_form port))
  | Some CP_Adv _            -> true
  | Some _                   -> false

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
   "intport " followed the name of the party (which in the case of a
   simulator will consists of the (unqualified by the root) name of
   the real functionality being simulated, followed by '.', followed
   by the party) *)

type local_context_base =
  | LCB_Bound   of EcIdent.t * form  (* bound identifier - state param or
                                        of message match clause *)
  | LCB_Var     of EcIdent.t * ty    (* local variable *)
  | LCB_EnvPort of form
  | LCB_IntPort of EcIdent.t * form  (* of type port *)

let lc_create (lcbs : local_context_base list) : local_context =
  [EcIdent.Mid.of_list
   (List.map
    (fun lcb ->
       match lcb with
       | LCB_Bound (id, form)   -> (id, form)
       | LCB_Var (id, ty)       ->
           (id, f_op EcCoreLib.CI_Witness.p_witness [ty] ty)
       | LCB_EnvPort func       ->
           (envport_id,
            (f_app envport_op [func] (tfun port_ty tbool)))
       | LCB_IntPort (id, port) -> (id, port))
    lcbs)]

let lc_find_key_from_sym (map : 'a EcIdent.Mid.t) (sym : symbol)
      : EcIdent.t option =
  EcIdent.Mid.fold_left
  (fun acc id _ ->
     match acc with
     | None -> if EcIdent.name id = sym then Some id else None
     | res  -> res)
  None
  map

let lc_update_var (lc : local_context) (id : symbol) (f : form)
      : local_context =
  let (lc_base, lc_rest) = (List.hd lc, List.tl lc) in
  let id = Option.get (lc_find_key_from_sym lc_base id) in
  EcIdent.Mid.change (fun _ -> Some f) id lc_base :: lc_rest

type lca_mode =      (* at end: *)
  | LCAM_NoSimp      (* don't simplify at all *)
  | LCAM_WeakSimp    (* settle for a weakly simplified formula *)
  | LCAM_StrongSimp  (* strongly simplify *)

let lc_apply_and_path_subst (mode : lca_mode) (gc : global_context)
    (lc : local_context) (path_subst : form -> form)
    (dbs : rewriting_dbs) (f : form) : form =
  let map =
    List.fold_left
    (fun acc nxt ->
       EcIdent.Mid.union (fun _ _ f -> Some f) acc nxt)
    (List.hd lc) (List.tl lc) in
  let subst =
    List.fold_left
    (fun acc (x, f) -> Fsubst.f_bind_local acc x f)
    Fsubst.f_subst_id (EcIdent.Mid.bindings map) in
  let f = path_subst f in
  let f = Fsubst.f_subst subst f in
  match mode with
  | LCAM_NoSimp     -> f
  | LCAM_WeakSimp   -> simplify_formula false gc dbs f
  | LCAM_StrongSimp -> simplify_formula true gc dbs f

let push (lc : local_context) (fr : local_context_frame) : local_context =
  lc @ [fr]

let make_and_push (lc : local_context) (bindings : (EcIdent.t * form) list)
      : local_context =
  push lc (EcIdent.Mid.of_list bindings)

let lc_pop (lc : local_context) : local_context =
  (if List.is_empty lc then failure "should not happen");
  List.take (List.length lc - 1) lc

let pp_local_context (env : env) (ppf : formatter) (lc : local_context) : unit =
  let pp_frame_entry (ppf : formatter) ((id, form) : EcIdent.t * form)
        : unit =
    fprintf ppf "@[%s ->@ %a@]" (EcIdent.name id) (pp_form env) form in
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
   otherwise, it'll be the relative address (wrt func_id) of the real
   functionality being simulated *)

type sim_state = {
  addr  : int list option;
  state : state
}

let set_addr_if_none_in_sim_state (ss : sim_state)
    (addr : int list) : sim_state =
  {ss with addr = Some (ss.addr |? addr)}

let update_state_in_sim_state (ss : sim_state)
    (new_state : state) : sim_state =
  {ss with state = new_state}

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
  | RWRC_IdealFunc of int list  *  (* relative address *)
                      int       *  (* base adversarial port index *)
                      symb_pair *  (* functionality *)
                      symbol       (* state name *)
  | RWRC_RealFunc  of int list  *  (* relative address *)
                      int       *  (* base adversarial port index *)
                      symb_pair *  (* functionality *)
                      symbol    *  (* party name *)
                      symbol       (* state name *)

let root_of_real_world_running_context (rwrc : real_world_running_context)
      : symbol =
  match rwrc with
  | RWRC_IdealFunc (_, _, (root, _), _)   -> root
  | RWRC_RealFunc (_, _, (root, _), _, _) -> root

let pp_relative_address (ppf : formatter) (addr : int list) : unit =
  fprintf ppf "[@[%a@]]"
  (EcPrinting.pp_list ";@ " pp_int) addr

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
  | RWSC_Env                  (* sending from environment *)
  | RWSC_Adv                  (* sending from adversary *)
  | RWSC_Func of int list  *  (* sending from functionality; relative address *)
                 symb_pair    (* functionality *)

let pp_real_world_sending_context (ppf : formatter)
    (rwsc : real_world_sending_context) : unit =
  match rwsc with
  | RWSC_Env           ->
      fprintf ppf "@[sending from environment@]"
  | RWSC_Adv           ->
      fprintf ppf "@[sending from adversary@]"
  | RWSC_Func (is, sp) ->
      fprintf ppf "@[sending from %a: %a@]"
      pp_relative_address is
      pp_symb_pair sp

type ideal_world_running_context =
  | IWRC_IdealFunc of int       *  (* adversarial port index *)
                      symb_pair *  (* functionality *)
                      symbol       (* state name *)
  | IWRC_MainSim   of int       *  (* adversarial port index *)
                      symb_pair *  (* main simulator *)
                      symbol       (* state name *)
  | IWRC_OtherSim  of int       *  (* adversarial port index *)
                      symb_pair *  (* other simulator *)
                      symbol    *  (* state name *)
                      int          (* index (from 0) into list of
                                      other simulators *)

let root_of_ideal_world_running_context (iwrc : ideal_world_running_context)
      : symbol =
  match iwrc with
  | IWRC_IdealFunc (_, (root, _), _)   -> root
  | IWRC_MainSim (_, (root, _), _)     -> root  
  | IWRC_OtherSim (_, (root, _), _, _) -> root

let pp_ideal_world_running_context (ppf : formatter)
    (iwrc : ideal_world_running_context) : unit =
  match iwrc with
  | IWRC_IdealFunc (i, sp, state_id)   ->
      fprintf ppf "@[running at@ %n:@ %a/@,%s@]"
      i
      pp_symb_pair sp
      state_id
  | IWRC_MainSim (i, sp, state_id)     ->
      fprintf ppf "@[running at@ %n:@ %a/@,%s@]"
      i
      pp_symb_pair sp
      state_id
  | IWRC_OtherSim (i, sp, state_id, _) ->
      fprintf ppf "@[running at@ %n:@ %a/@,%s@]"
      i
      pp_symb_pair sp
      state_id

type ideal_world_sending_context =
  | IWSC_Env                        (* sending from environment *)
  | IWSC_Adv                        (* sending from adversary *)
  | IWSC_IdealFunc of symb_pair     (* functionality *)
  | IWSC_MainSim   of int       *   (* adversarial port index *)
                      symb_pair     (* main simulator *)
  | IWSC_OtherSim  of int       *   (* adversarial port index *)
                      symb_pair *   (* other simulator *)
                      int           (* index (from 0) into list of
                                       other simulators *)

let pp_ideal_world_sending_context (ppf : formatter)
    (iwrc : ideal_world_sending_context) : unit =
  match iwrc with
  | IWSC_Env                 ->
      fprintf ppf "@[sending from environment@]"
  | IWSC_Adv                 ->
      fprintf ppf "@[sending from adversary@]"
  | IWSC_IdealFunc sp        ->
      fprintf ppf "@[sending from %a@]"
      pp_symb_pair sp
  | IWSC_MainSim (i, sp)     ->
      fprintf ppf "@[sending from %n:@ %a@]"
      i
      pp_symb_pair sp
  | IWSC_OtherSim (i, sp, _) ->
      fprintf ppf "@[sending from %n:@ %a@]"
      i
      pp_symb_pair sp

type config_gen = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  w    : worlds;
  ig   : int  (* input guard of interface - first adversarial *)
}             (* port index *not* used by worlds, and so available *)
              (* to environment (0 is always available to the environment, *)
              (* but used for communication between root of environment, *)
              (* ([], 0), and root of adversary, (adv, 0)) *)

type config_real = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  rw   : real_world;
  ig   : int;
  rws  : real_world_state;
  ctrl : control;
}

type config_ideal = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  iw   : ideal_world;
  ig   : int;
  iws  : ideal_world_state;
  ctrl : control;
}

type config_real_running = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  rw   : real_world;
  ig   : int;
  rws  : real_world_state;
  rwrc : real_world_running_context;
  path : symbol list;
  lc   : local_context;
  ins  : instr_interp list
}

type config_ideal_running = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  iw   : ideal_world;
  ig   : int;
  iws  : ideal_world_state;
  iwrc : ideal_world_running_context;
  path : symbol list;
  lc   : local_context;
  ins  : instr_interp list
}

type config_real_sending = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  rw   : real_world;
  ig   : int;
  rws  : real_world_state;
  rwsc : real_world_sending_context;
  sme  : sent_msg_expr_tyd
}

type config_ideal_sending = {
  maps : maps_tyd;
  gc   : global_context;
  pi   : prover_infos;
  dbs  : rewriting_dbs;
  iw   : ideal_world;
  ig   : int;
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

let rewriting_dbs_of_config (conf : config) : rewriting_dbs =
  match conf with
  | ConfigGen c          -> c.dbs
  | ConfigReal c         -> c.dbs
  | ConfigIdeal c        -> c.dbs
  | ConfigRealRunning c  -> c.dbs
  | ConfigIdealRunning c -> c.dbs
  | ConfigRealSending c  -> c.dbs
  | ConfigIdealSending c -> c.dbs

let control_of_real_or_ideal_config (conf : config) : control =
  match conf with
  | ConfigReal c  -> c.ctrl
  | ConfigIdeal c -> c.ctrl
  | _             -> raise ConfigError

let loc_of_running_config_next_instr (conf : config) : EcLocation.t option =
  match conf with
  | ConfigRealRunning c  ->
      (match c.ins with
       | []       -> failure "cannot happen"
       | ins :: _ -> Some (loc ins))
  | ConfigIdealRunning c ->
      (match c.ins with
       | []       -> failure "cannot happen"
       | ins :: _ -> Some (loc ins))
  | _                    -> None

let typecheck_and_pp_sent_msg_expr (conf : config) (sme : sent_msg_expr)
      : string =
  let env = env_of_config conf in
  let sme = inter_check_sent_msg_expr (maps_of_config conf) env sme in
  pp_sent_msg_expr_to_string env sme

(* pretty printer for configurations *)

let party_and_sub_fun_states (maps : maps_tyd) (rws : real_world_state)
    (addr : int list) (sp : symb_pair) (path : path) (base : int)
      : (int option * symbol * path option * state) list =
  let root = fst sp in
  let ft = IdPairMap.find sp maps.fun_map in
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let num_args = IdMap.cardinal rfbt.params in
  let num_adv_pis_of_parties =
    num_adv_pis_of_parties_of_real_fun maps root ft in
  let of_parties =
    List.map
    (fun (pty, state) ->
       let adv_pi_opt =
         match get_adv_info_of_party_of_real_fun maps root base
               ft pty with
         | None                  -> None
         | Some (_, _, _, advpi) -> Some advpi in
       (adv_pi_opt, pty, None, state))
    (IdMap.bindings (real_state_of_fun_state (ILMap.find addr rws))) in
  let of_sub_funs =
    List.mapi
    (fun i (id, (_, _, clone)) ->
       (Some (base + 1 + num_adv_pis_of_parties + i),
        id,
        Some (path @ [clone]),
        ideal_state_of_fun_state
        (ILMap.find (addr @ [1 + num_args + i]) rws)))
    (IdMap.bindings rfbt.sub_funs) in
  of_parties @ of_sub_funs

let pp_state (gc : global_context) (ppf : formatter)
    (state : state) : unit =
  let env = env_of_gc gc in
  match state.args with
  | []   -> fprintf ppf "%s" state.id
  | args ->
      fprintf ppf "@[%s@,(@[%a@])@]" state.id
      (EcPrinting.pp_list ",@ " (pp_form env)) args

let pp_party_or_sub_fun_info (gc : global_context) (ppf : formatter)
    ((adv_pi_opt, id, path_opt, state) :
       (int option) * symbol * (path option) * state) : unit =
  match adv_pi_opt, path_opt with
  | None,        None      ->
      fprintf ppf "@[%s:@ %a@]" id (pp_state gc) state
  | Some adv_pi, None      ->
      fprintf ppf "@[%s(%d):@ %a@]" id adv_pi (pp_state gc) state
  | None,        Some path ->
      fprintf ppf "@[%s[%a]:@ %a@]" id pp_path path (pp_state gc) state
  | Some adv_pi, Some path ->
      fprintf ppf "@[%s[%a](%d):@ %a@]"
      id pp_path path adv_pi (pp_state gc) state

let pp_adv_pi_opt_sym_state_list (gc : global_context) (ppf : formatter)
    (infos : (int option * symbol * path option * state) list) : unit =
  EcPrinting.pp_list ",@ " (pp_party_or_sub_fun_info gc) ppf infos

let pp_real_world_with_states (maps : maps_tyd) (gc : global_context)
    (rws : real_world_state) (ppf : formatter) (rw : real_world) : unit =
  let rec pp_real_world (addr : int list) (ppf : formatter)
      ((sp, i, path, rwas) : real_world) : unit =
    let psfs = party_and_sub_fun_states maps rws addr sp path i in
    match rwas with
    | [] ->
      fprintf ppf "@[%a@,[@[%a@]]@]"
      pp_world_fun_info (sp, i, path) (pp_adv_pi_opt_sym_state_list gc) psfs
    | _  ->
      fprintf ppf "@[%a@,[@[%a@]]@,(@[%a@])@]"
      pp_world_fun_info (sp, i, path) (pp_adv_pi_opt_sym_state_list gc) psfs
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
    | RWA_Real rw             -> pp_real_world addr ppf rw
    | RWA_Ideal (sp, i, path) ->
        let ideal_st = ideal_state_of_fun_state (ILMap.find addr rws) in
        fprintf ppf "%a@,[@[%a@]]"
        pp_world_fun_info (sp, i, path)
        (pp_state gc) ideal_st in
  pp_real_world [] ppf rw

let pp_sim_state (gc : global_context) (ppf : formatter)
    (sim_st : sim_state) : unit =
  let pp_addr (ppf : formatter) (f_opt : int list option) : unit =
    match f_opt with
    | None     -> fprintf ppf "uninitialized"
    | Some rel ->
        fprintf ppf "@[initialized:@ @[func ++@ %a@]@]"
        pp_relative_address rel in
  fprintf ppf "@[%a /@ %a@]"
  pp_addr sim_st.addr
  (pp_state gc) sim_st.state

let rec pp_sims_with_states (i : int) (gc : global_context)
    (iws : ideal_world_state) (ppf : formatter)
    (sims : (symb_pair * int * int list * path) list) : unit =
  match sims with
  | []        -> ()
  | [spi]     ->
    fprintf ppf " *@ @[%a@,[@[%a@]]@]"
    pp_world_sim_info spi
    (pp_sim_state gc) (List.nth iws.other_sims_states i)
  | sim :: sims ->
    fprintf ppf " *@ @[%a@,[@[%a@]]%a@]"
    pp_world_sim_info sim
    (pp_sim_state gc) (List.nth iws.other_sims_states i)
    (pp_sims_with_states (i + 1) gc iws) sims

let pp_ideal_world_with_states (gc : global_context)
    (iws : ideal_world_state) (ppf : formatter) (iw : ideal_world) : unit =
  fprintf ppf "@[@[%a@,[@[%a]@]@] /@ @[@[%a@,[@[%a@]]@]%a@]@]"
  pp_world_fun_info iw.iw_ideal_func
  (pp_state gc) iws.ideal_fun_state
  pp_world_sim_info iw.iw_main_sim
  (pp_sim_state gc) iws.main_sim_state
  (pp_sims_with_states 0 gc iws) iw.iw_other_sims

let pp_global_context_msg (ppf : formatter) (gc : global_context) : unit =
  fprintf ppf
  "@[global context:@ %a@]"
  pp_global_context gc

let pp_local_context_msg (env : env) (ppf : formatter)
    (lc : local_context) : unit =
  fprintf ppf
  "@[local context:@ %a@]"
  (pp_local_context env) lc

(* path will have length >= 2, and we omit the first two components,
   "Top" and the root *)

let pp_theory_path_msg (ppf : formatter) (path : path) : unit =
  fprintf ppf
  "@[theory@ path:@ %a@]"
  pp_path path

let pp_worlds_msg (ppf : formatter) (w : worlds) : unit =
  fprintf ppf
  "@[worlds:@ %a@]"
  pp_worlds w

let pp_real_world_with_states_msg (maps : maps_tyd) (gc : global_context)
    (rws : real_world_state) (ppf : formatter) (rw : real_world) : unit =
  fprintf ppf
  "@[real world:@ %a@]"
  (pp_real_world_with_states maps gc rws) rw

let pp_ideal_world_with_states_msg (gc : global_context)
    (iws : ideal_world_state) (ppf : formatter) (iw : ideal_world) : unit =
  fprintf ppf
  "@[ideal world:@ %a@]"
  (pp_ideal_world_with_states gc iws) iw

let pp_input_guard_msg (ppf : formatter) (n : int) : unit =
  fprintf ppf "@[input guard:@ %d@]" n

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
      (pp_ideal_world_with_states_msg c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_control_msg c.ctrl
  | ConfigRealRunning c  ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n%a@\n@\n%a@]"
      pp_global_context_msg c.gc
      (pp_real_world_with_states_msg c.maps c.gc c.rws) c.rw
      pp_input_guard_msg c.ig
      pp_real_world_running_context c.rwrc
      pp_theory_path_msg c.path
      (pp_local_context_msg (env_of_gc c.gc)) c.lc
  | ConfigIdealRunning c ->
      fprintf ppf
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n%a@\n@\n%a@]"
      pp_global_context_msg c.gc
      (pp_ideal_world_with_states_msg c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_ideal_world_running_context c.iwrc
      pp_theory_path_msg c.path
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
      "@[%a@\n@\n%a@\n@\n%a@\n%a@\n@\n@[message:@ %a@]@]"
      pp_global_context_msg c.gc
      (pp_ideal_world_with_states_msg c.gc c.iws) c.iw
      pp_input_guard_msg c.ig
      pp_ideal_world_sending_context c.iwsc
      (pp_sent_msg_expr_tyd (env_of_gc c.gc)) c.sme

let pp_sent_msg_expr_tyd_in_config (ppf : formatter) (c : config)
    (sme : sent_msg_expr_tyd) : unit =
  pp_sent_msg_expr_tyd (env_of_config c) ppf sme

let create_gen_config (root : symbol) (maps : maps_tyd) (env : env)
    (fe : fun_expr) : config =
  let fet = inter_check_real_fun_expr root maps fe in
  let (w, ig) = fun_expr_tyd_to_worlds maps fet in
  let gc = gc_create env in
  let pi = default_prover_infos () in
  let dbs = default_rewriting_dbs in
  ConfigGen {maps = maps; gc = gc; pi = pi; dbs = dbs; w = w; ig = ig}

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

let modify_rewriting_dbs_config (conf : config) (mod_dbs : mod_dbs)
      : config =
  match conf with
  | ConfigGen c          ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigGen {c with dbs = dbs}
  | ConfigReal c         ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigReal {c with dbs = dbs}
  | ConfigIdeal c        ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigIdeal {c with dbs = dbs}
  | ConfigRealRunning c  ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigRealRunning {c with dbs = dbs}
  | ConfigIdealRunning c ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigIdealRunning {c with dbs = dbs}
  | ConfigRealSending c  ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigRealSending {c with dbs = dbs}
  | ConfigIdealSending c ->
      let dbs =
        modify_rewriting_dbs (env_of_gc c.gc) c.dbs mod_dbs in
      ConfigIdealSending {c with dbs = dbs}

let pp_rewriting_dbs_config (ppf : Format.formatter)
    (conf : config) : unit =
  pp_rewriting_dbs ppf (rewriting_dbs_of_config conf)

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

let add_hyp_to_config (conf : config) (id : psymbol) (pform : pformula)
      : config =
  match conf with
  | ConfigGen c          ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigGen {c with gc = gc}
  | ConfigReal c         ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigReal {c with gc = gc}
  | ConfigIdeal c        ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigIdeal {c with gc = gc}
  | ConfigRealRunning c  ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigRealRunning {c with gc = gc}
  | ConfigIdealRunning c ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigIdealRunning {c with gc = gc}
  | ConfigRealSending c  ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigRealSending {c with gc = gc}
  | ConfigIdealSending c ->
      let gc = gc_add_hyp c.gc id pform in
      ConfigIdealSending {c with gc = gc}

let add_hyp_to_config_make_unique (conf : config) (id : psymbol)
    (pform : pformula) : config * symbol =
  let l = loc id in
  let id = gc_make_unique_id (gc_of_config conf) (unloc id) in
  (add_hyp_to_config conf (mk_loc l id) pform, id)

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
  let init_of_subfuns (subs : porsf_info IdMap.t) (nargs : int)
      (addr : int list) : (int list * fun_state) list =
    let sps =
      List.map (fun (_, (root, id, _)) -> (root, id))
      (IdMap.bindings subs) in
    List.mapi
    (fun i sp ->
       (addr @ [1 + nargs + i],
        IdealState
         (state_no_args
          (initial_state_id_of_ideal_fun_tyd
           (IdPairMap.find sp maps.fun_map)))))
    sps in
  let rec init_of_rw ((sp, _, _, rwas) : real_world) (addr : int list)
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
    | RWA_Real rw          -> init_of_rw rw addr
    | RWA_Ideal (sp, _, _) ->
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
      {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; rw = rw; ig = c.ig;
       rws = rws; ctrl = CtrlEnv}
  | _           -> raise ConfigError

let initial_ideal_world_state (maps : maps_tyd) (iw : ideal_world)
      : ideal_world_state =
  let ideal_fun_state =
    state_no_args
    (initial_state_id_of_ideal_fun_tyd
     (IdPairMap.find (proj3_1 iw.iw_ideal_func) maps.fun_map)) in
  let main_sim_state =
    {addr  = None;
     state =
       state_no_args
       (initial_state_id_of_sim_tyd
        (IdPairMap.find
         (let (x, _, _, _) = iw.iw_main_sim in x)
         maps.sim_map))} in
  let other_sims_states =
    List.map
    (fun (sp, _, _, _) ->
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
      {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; iw = iw; ig = c.ig;
       iws = iws; ctrl = CtrlEnv}
  | _           -> raise ConfigError

(* sending messages and stepping configurations *)

(* effects *)

type eff =
  | EffOK                          (* step succeeded (not random
                                      assignment), and new configuration
                                      is running or sending *)
  | EffRand of symbol              (* step added ident representing
                                      random choice to global context,
                                      and new configuration is running *)
  | EffMsgOut of string * control  (* a message was output, and new
                                      configuration is real or ideal;
                                      control says who has control *)
  | EffFailOut                     (* fail was output, and new
                                      configuration is real or ideal *)

let pp_eff (ppf : formatter) (e : eff) : unit =
  match e with
  | EffOK                       -> fprintf ppf "EffectOK"
  | EffRand id                  -> fprintf ppf "@[EffectRand: %s@]" id
  | EffMsgOut (pp_sme, ctrl)    ->
      fprintf ppf "@[EffectMsgOut:@ %a:@ %s@]" pp_control ctrl pp_sme
  | EffFailOut                  -> fprintf ppf "EffectFailOut"

let fail_out_of_running_or_sending_config (conf : config) : config * eff =
  match conf with
  | ConfigRealRunning c  ->
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; rw = c.rw;
        ig = c.ig; rws = c.rws; ctrl = CtrlEnv},
       EffFailOut)
  | ConfigIdealRunning c ->
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; iw = c.iw;
        ig = c.ig; iws = c.iws; ctrl = CtrlEnv},
       EffFailOut)
  | ConfigRealSending c  ->
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; rw = c.rw;
        ig = c.ig; rws = c.rws; ctrl = CtrlEnv},
       EffFailOut)
  | ConfigIdealSending c ->
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; iw = c.iw;
        ig = c.ig; iws = c.iws; ctrl = CtrlEnv},
       EffFailOut)
  | _                    -> raise ConfigError

let msg_out_of_sending_config (conf : config) (ctrl : control)
      : config * eff =
  match conf with
  | ConfigRealSending c  ->
      let pp_sme = pp_sent_msg_expr_to_string (env_of_gc c.gc) c.sme in
      (ConfigReal
       {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; rw = c.rw;
        ig = c.ig; rws = c.rws; ctrl = ctrl},
       EffMsgOut (pp_sme, ctrl))
  | ConfigIdealSending c ->
      let pp_sme = pp_sent_msg_expr_to_string (env_of_gc c.gc) c.sme in
      (ConfigIdeal
       {maps = c.maps; gc = c.gc; pi = c.pi; dbs = c.dbs; iw = c.iw;
        ig = c.ig; iws = c.iws; ctrl = ctrl},
       EffMsgOut (pp_sme, ctrl))
  | _                    -> raise ConfigError

let simplify_sent_msg_expr (gc : global_context) (dbs : rewriting_dbs)
    (sme : sent_msg_expr_tyd) : sent_msg_expr_tyd =
  let simpl = simplify_formula false gc dbs in
  let simpl_port = simplify_port gc dbs in
  match sme with
  | SMET_Ord sme    ->
      SMET_Ord
      {mode           = sme.mode;
       dir            = sme.dir;
       src_port_form  = simpl_port sme.src_port_form;
       path           = sme.path;
       args           = List.map simpl sme.args;
       dest_port_form = simpl_port sme.dest_port_form}
  | SMET_EnvAdv sme ->
      SMET_EnvAdv
      {src_port_form  = simpl_port sme.src_port_form;
       dest_port_form = simpl_port sme.dest_port_form}

let check_sme_port_index_consistency_core
    (error : string -> EcLocation.t -> unit)
    (loc_source : EcLocation.t) (loc_dest : EcLocation.t)
    (maps : maps_tyd) (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (sme : sent_msg_expr_tyd) : unit =
  let check_consist (sme : sent_msg_expr_ord_tyd) (port_form : form)
      (src_or_dest_str : string) (loc_src_or_dest : EcLocation.t)  : unit =
    match sme.path.inter_id_path with
    | [root; comp; sub] ->
        let porti = get_pi_of_sub_interface maps root comp sub in
        if try
             equal_port_index_of_port gc pi dbs port_form porti
           with
           | ECProofEngine -> false
        then ()
        else error src_or_dest_str loc_src_or_dest
    | [_; _]            ->
        if try
             equal_port_index_of_port gc pi dbs port_form 1
           with
           | ECProofEngine -> false
        then ()
        else error src_or_dest_str loc_src_or_dest
    | _                 -> failure "cannot happen" in
  match sme with
  | SMET_Ord sme ->
      if sme.dir = In
      then let dest_port = sme.dest_port_form in
           check_consist sme dest_port "destination" loc_dest
      else let source_port = sme.src_port_form in
           check_consist sme source_port "source" loc_source
  | _            -> ()

let check_sme_port_index_consistency :
      maps_tyd -> global_context -> prover_infos -> rewriting_dbs ->
      sent_msg_expr_tyd -> unit =
  check_sme_port_index_consistency_core
  (fun _ _ -> failure "should not happen")
  _dummy _dummy

let inter_check_sent_msg_expr_consistency
    (maps : maps_tyd) (gc : global_context) (pi : prover_infos)
    (dbs : rewriting_dbs) (sme : sent_msg_expr) : sent_msg_expr_tyd =
  let sme_ty = inter_check_sent_msg_expr maps (env_of_gc gc) sme in
  let sme_ty = simplify_sent_msg_expr gc dbs sme_ty in
  let loc_source = loc_of_src_of_sent_msg_expr sme in
  let loc_dest = loc_of_dest_of_sent_msg_expr sme in
  check_sme_port_index_consistency_core
  (fun port_index_kind loc_of_port_index ->
    error_message loc_of_port_index
    (fun ppf ->
       fprintf ppf
       "@[%s@ port@ index@ is@ (may@ be)@ inconsistent@ with@ message@ path@]"
       port_index_kind))
  loc_source loc_dest maps gc pi dbs sme_ty;
  sme_ty

let send_message_to_real_or_ideal_config
    (conf : config) (sme : sent_msg_expr) : config =
  match conf with
  | ConfigReal c  ->
      let sme =
        inter_check_sent_msg_expr_consistency c.maps c.gc c.pi c.dbs sme in
      ConfigRealSending
      {maps = c.maps;
       gc   = c.gc;
       pi   = c.pi;
       dbs  = c.dbs;
       rw   = c.rw;
       ig   = c.ig;
       rws  = c.rws;
       rwsc = if c.ctrl = CtrlEnv then RWSC_Env else RWSC_Adv;
       sme  = sme}
  | ConfigIdeal c ->
      let sme =
        inter_check_sent_msg_expr_consistency c.maps c.gc c.pi c.dbs sme in
      ConfigIdealSending
      {maps = c.maps;
       gc   = c.gc;
       pi   = c.pi;
       dbs  = c.dbs;
       iw   = c.iw;
       ig   = c.ig;
       iws  = c.iws;
       iwsc = if c.ctrl = CtrlEnv then IWSC_Env else IWSC_Adv;
       sme  = sme}
  | _             -> raise ConfigError

exception StepBlockedIf
exception StepBlockedMatch
exception StepBlockedPortOrAddrCompare

(* start of functions that can be used for stepping in both real and
   ideal worlds *)

let step_assign (gc : global_context) (lc : local_context)
    (path_subst : form -> form) (dbs : rewriting_dbs) (lhs : lhs)
    (form : form) : local_context =
  let form = lc_apply_and_path_subst LCAM_WeakSimp gc lc path_subst dbs form in
  match lhs with
  | LHSSimp id   -> lc_update_var lc (unloc id) form
  | LHSTuple ids ->
      let tys =
        match form.f_ty.ty_node with
        | Ttuple tys -> tys
        | _          -> failure "should not happen" in
      List.fold_lefti
      (fun acc i id ->
         let pr = f_proj form i (List.nth tys i) in
         let pr = simplify_formula true gc dbs pr in
         lc_update_var acc (unloc id) pr)
      lc
      ids

let step_sample (gc : global_context) (lc : local_context)
    (path_subst : form -> form) (dbs : rewriting_dbs)
    (lhs : lhs) (form : form)
      : global_context * local_context * symbol =
  let form =
    lc_apply_and_path_subst LCAM_StrongSimp gc lc path_subst dbs form in
  let ty = Option.get (as_tdistr (EcEnv.Ty.hnorm form.f_ty (env_of_gc gc))) in
  match lhs with
  | LHSSimp id   ->
      let (gc, rand) = gc_add_rand gc "rand" "Hrand" ty form in
      let lc = lc_update_var lc (unloc id) (f_local rand ty) in
      (gc, lc, EcIdent.name rand)
  | LHSTuple ids ->
      let (gc, rand) = gc_add_rand gc "rand" "Hrand" ty form in
      let tys =
        match ty.ty_node with
        | Ttuple tys -> tys
        | _          -> failure "should not happen" in
      let lc =
        List.fold_lefti
        (fun acc i id ->
           let pr_rand = f_proj (f_local rand ty) i (List.nth tys i) in
           lc_update_var acc (unloc id) pr_rand)
        lc
        ids in
      (gc, lc, EcIdent.name rand)

let step_if_then_else (gc : global_context) (lc : local_context)
    (path_subst : form -> form) (pi : prover_infos) (dbs : rewriting_dbs)
    (form : form) (inss_then : instr_interp list)
    (inss_else_opt : instr_interp list option) : instr_interp list =
  let expr_gc_form =
    lc_apply_and_path_subst LCAM_NoSimp gc lc path_subst dbs form in
  if try eval_bool_form_to_bool gc pi dbs expr_gc_form with
     | ECProofEngine -> raise StepBlockedIf
  then inss_then
  else (odfl [] inss_else_opt)

let step_match (gc : global_context) (lc : local_context)
    (path_subst : form -> form) (pi : prover_infos) (dbs : rewriting_dbs)
    (form : form) (clauses : match_clause_interp list)
      : local_context * instr_interp list =
  let form = lc_apply_and_path_subst LCAM_NoSimp gc lc path_subst dbs form in
  let (form_constr, form_args) =
    try deconstruct_datatype_value gc pi dbs form with
    | ECProofEngine -> raise StepBlockedMatch in
  let rec find_match (clauses : match_clause_interp list)
        : local_context * instr_interp list =
    match clauses with
    | []                                    -> failure "should not happen"
    | (constr, (bindings, inss)) :: clauses ->
        if constr = form_constr
        then let ids =
               List.map (fun (id, _) -> unloc id) bindings in
             let bindings = List.combine ids form_args in
             let lc = make_and_push lc bindings in
             (lc, inss @ [mk_loc _dummy Pop])
        else find_match clauses
  in find_match clauses

(* end of functions that can be used for stepping in both real and
   ideal worlds *)

(* real world send-and-transition *)

let rw_step_send_and_transition_from_ideal_fun (c : config_real_running)
    (pi : prover_infos) (dbs : rewriting_dbs) (rel : int list)
    (base : int) (fun_sp : symb_pair) (iip : string list) (msg : string)
    (msg_args : form list) (port_form : form option)
    (new_rws : real_world_state)
      : config * eff =
  let (root, _) = fun_sp in
  match port_form with
  | None           ->  (* adversarial message to adversary *)
      let path = {inter_id_path = root :: iip; msg = msg} in
      let sme =
        SMET_Ord
        {mode           = Adv;
         dir            = Out;
         src_port_form  =
           make_port_form
           (addr_concat_form_from_list_smart func_form rel)
           (int_form 1);
         path           = path;
         args           = msg_args;
         dest_port_form =
           make_port_form adv_addr_form (int_form base)} in
      let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
      (ConfigRealSending
       {maps = c.maps;
        gc   = c.gc;
        pi   = c.pi;
        dbs  = c.dbs;
        rw   = c.rw;
        ig   = c.ig;
        rws  = new_rws;
        rwsc = RWSC_Func (rel, fun_sp);
        sme  = sme},
       EffOK)
  | Some port_form ->  (* direct message to environment (or parent) *)
      let (comp, sub) =
        match iip with
        | [comp; sub] -> (comp, sub)
        | _           -> failure "should not happen" in
      let source_pi = get_pi_of_sub_interface c.maps root comp sub in
      let path = {inter_id_path = root :: iip; msg = msg} in
      let sme =
        SMET_Ord
        {mode           = Dir;
         dir            = Out;
         src_port_form  =
           make_port_form
           (addr_concat_form_from_list_smart func_form rel)
           (int_form source_pi);
         path           = path;
         args           = msg_args;
         dest_port_form = port_form} in
      let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
      (ConfigRealSending
       {maps = c.maps;
        gc   = c.gc;
        pi   = c.pi;
        dbs  = c.dbs;
        rw   = c.rw;
        ig   = c.ig;
        rws  = new_rws;
        rwsc = RWSC_Func (rel, fun_sp);
        sme  = sme},
       EffOK)

let rw_step_send_and_transition_from_real_fun_party_to_arg_or_sub_fun
    (c : config_real_running) (pi : prover_infos) (dbs : rewriting_dbs)
    (rel : int list) (fun_sp : symb_pair) (ft : fun_tyd)
    (pty_id : symbol) (iip : symbol list) (msg : symbol)
    (msg_args : form list) (port_form : form option)
    (new_rws : real_world_state) (sub : symbol)
    (child_i : int) (dir_sp : symb_pair) : config * eff =
  assert (Option.is_none port_form);
  let (dir_root, dir_comp) = dir_sp in
  let pty_internal_pi = get_internal_pi_of_party_of_real_fun ft pty_id in
  let source_port =
    make_port_form
    (addr_concat_form_from_list_smart func_form rel)
    (int_form pty_internal_pi) in
  let dest_pi = get_pi_of_sub_interface c.maps dir_root dir_comp sub in
  let dest_port =
    make_port_form
    (addr_concat_form_from_list_smart func_form (rel @ [child_i]))
    (int_form dest_pi) in
  let iip_new = dir_root :: dir_comp :: List.tl iip in
  let path_new = {inter_id_path = iip_new; msg = msg} in
  let sme =
    SMET_Ord
    {mode           = Dir;
     dir            = In;
     src_port_form  = source_port;
     path           = path_new;
     args           = msg_args;
     dest_port_form = dest_port} in
  let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
  (ConfigRealSending
   {maps = c.maps;
    gc   = c.gc;
    pi   = c.pi;
    dbs  = c.dbs;
    rw   = c.rw;
    ig   = c.ig;
    rws  = new_rws;
    rwsc = RWSC_Func (rel, fun_sp);
    sme  = sme},
   EffOK)

let rw_step_send_and_transition_from_real_fun_party_to_env_or_adv
    (c : config_real_running) (pi : prover_infos) (dbs : rewriting_dbs)
    (rel : int list) (base : int) (fun_sp : symb_pair) (ft : fun_tyd)
    (pty_id : symbol) (iip : symbol list) (msg : symbol) (msg_args : form list)
    (port_form : form option) (new_rws : real_world_state)
    (comp : symbol) (sub : symbol) : config * eff =
  let (root, _) = fun_sp in
  match port_form with
  | None           ->  (* adversarial message to adversary *)
      let (_, _, pty_pi, adv_pi) =
        Option.get
        (get_adv_info_of_party_of_real_fun c.maps root base
         ft pty_id) in
      let path = {inter_id_path = root :: iip; msg = msg} in
      let sme =
        SMET_Ord
        {mode           = Adv;
         dir            = Out;
         src_port_form  =
           make_port_form
           (addr_concat_form_from_list_smart func_form rel)
           (int_form pty_pi);
         path           = path;
         args           = msg_args;
         dest_port_form =
           make_port_form adv_addr_form (int_form adv_pi)} in
      let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
      (ConfigRealSending
       {maps = c.maps;
        gc   = c.gc;
        pi   = c.pi;
        dbs  = c.dbs;
        rw   = c.rw;
        ig   = c.ig;
        rws  = new_rws;
        rwsc = RWSC_Func (rel, fun_sp);
        sme  = sme},
       EffOK)
  | Some port_form ->  (* direct message to environment (or parent) *)
      let source_pi = get_pi_of_sub_interface c.maps root comp sub in
      let path = {inter_id_path = root :: iip; msg = msg} in
      let sme =
        SMET_Ord
        {mode           = Dir;
         dir            = Out;
         src_port_form  =
           make_port_form
           (addr_concat_form_from_list_smart func_form rel)
           (int_form source_pi);
         path           = path;
         args           = msg_args;
         dest_port_form = port_form} in
      let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
      (ConfigRealSending
       {maps = c.maps;
        gc   = c.gc;
        pi   = c.pi;
        dbs  = c.dbs;
        rw   = c.rw;
        ig   = c.ig;
        rws  = new_rws;
        rwsc = RWSC_Func (rel, fun_sp);
        sme  = sme},
       EffOK)

let rw_step_send_and_transition_from_real_fun_party (c : config_real_running)
    (pi : prover_infos) (dbs : rewriting_dbs) (rel : int list) (base : int)
    (fun_sp : symb_pair) (pty_id : symbol) (iip : symbol list)
    (msg : symbol) (msg_args : form list) (port_form : form option)
    (new_rws : real_world_state) : config * eff =
  let (comp, sub) =
    match iip with
    | [comp; sub] -> (comp, sub)
    | _           -> failure "should not happen" in
  let ft = IdPairMap.find fun_sp c.maps.fun_map in
  match get_child_index_and_comp_inter_porsfi_of_param_or_sub_fun_of_real_fun
        c.maps ft comp with
  | None                   ->
      rw_step_send_and_transition_from_real_fun_party_to_env_or_adv
      c pi dbs rel base fun_sp ft pty_id iip msg msg_args port_form new_rws
      comp sub
  | Some (child_i, (root, id, _)) ->
      rw_step_send_and_transition_from_real_fun_party_to_arg_or_sub_fun
      c pi dbs rel fun_sp ft pty_id iip msg msg_args port_form
      new_rws sub child_i (root, id)

let rw_step_send_and_transition (c : config_real_running)
    (path_subst : form -> form) (pi : prover_infos)
    (dbs : rewriting_dbs) (s_and_t : send_and_transition_tyd)
      : config * eff =
  let {msg_expr; state_expr} = s_and_t in
  let {path; args = msg_args; port_expr} = msg_expr in
  let {inter_id_path = iip; msg} = unloc path in
  let msg_args =
    List.map
    (fun arg ->
       lc_apply_and_path_subst LCAM_WeakSimp c.gc c.lc path_subst dbs arg)
    (unloc msg_args) in
  let port_form =
    match port_expr with
    | None      -> None
    | Some expr ->
        let port =
          lc_apply_and_path_subst LCAM_NoSimp c.gc c.lc path_subst dbs expr in
        Some (simplify_port c.gc dbs port) in
  let {UcTypedSpec.id = state_id; UcTypedSpec.args = state_args} =
    state_expr in
  let state_id = unloc state_id and state_args = unloc state_args in
  let state_args =
    List.map
    (fun arg ->
       lc_apply_and_path_subst LCAM_WeakSimp c.gc c.lc path_subst dbs arg)
    state_args in
  let new_state = {id = state_id; args = state_args} in
  let new_rws =
    match c.rwrc with
    | RWRC_IdealFunc (rel, _, _, _)          ->
        ILMap.update rel (fun _ -> Some (IdealState new_state)) c.rws
    | RWRC_RealFunc (rel, _, _, party_id, _) ->
        let old_real_fun_state =
          real_state_of_fun_state (ILMap.find rel c.rws) in
        let new_real_fun_state =
          IdMap.update party_id (fun _ -> Some new_state)
          old_real_fun_state in
        ILMap.update rel
        (fun _ -> Some (RealState new_real_fun_state)) c.rws in
  match c.rwrc with
  | RWRC_IdealFunc (rel, base, fun_sp, _)          ->
      rw_step_send_and_transition_from_ideal_fun c pi dbs rel base fun_sp
      iip msg msg_args port_form new_rws
  | RWRC_RealFunc (rel, base, fun_sp, party_id, _) ->
      rw_step_send_and_transition_from_real_fun_party c pi dbs rel base fun_sp
      party_id iip msg msg_args port_form new_rws

let step_real_running_config (c : config_real_running) (pi : prover_infos)
    (dbs : rewriting_dbs) : config * eff =
  let rec handle_pops (rest : instr_interp list) (lc : local_context)
        : instr_interp list * local_context =
    (assert (not (List.is_empty rest));
     if unloc (List.hd rest) = Pop
     then handle_pops (List.tl rest) (lc_pop lc)
     else (rest, lc)) in
  let rec check_only_pops (rest : instr_interp list) : bool =
    match rest with
    | []            -> true
    | instr :: rest -> unloc instr = Pop && check_only_pops rest in
  let inss = c.ins in
  assert (not (List.is_empty inss));
  let (next, rest) = (List.hd inss, List.tl inss) in
  let path_subst : form -> form =
    let root = root_of_real_world_running_context c.rwrc in
    cond_subst_path_prefix_in_form ["Top"; "UC___" ^ root] c.path in
  match unloc next with
  | Assign (lhs, expr)                   ->
      let lc = step_assign c.gc c.lc path_subst dbs lhs expr in
      let (rest, lc) = handle_pops rest lc in
      (ConfigRealRunning {c with lc = lc; ins = rest},
       EffOK)
  | Sample (lhs, expr)                   ->
      let (gc, lc, id) = step_sample c.gc c.lc path_subst dbs lhs expr in
      let (rest, lc) = handle_pops rest lc in
      (ConfigRealRunning {c with gc = gc; lc = lc; ins = rest},
       EffRand id)
  | ITE (expr, inss_then, inss_else_opt) ->
      let inss =
        step_if_then_else c.gc c.lc path_subst pi dbs
        expr inss_then inss_else_opt in
      let (rest, _) = handle_pops (inss @ rest) c.lc in
      (ConfigRealRunning {c with ins = rest}, EffOK)
  | Match (expr, clauses)                ->
      let (lc, inss) = step_match c.gc c.lc path_subst pi dbs expr clauses in
      let (rest, lc) = handle_pops (inss @ rest) lc in
      (ConfigRealRunning {c with lc = lc; ins = rest},
       EffOK)
  | SendAndTransition s_and_t            ->
      assert (check_only_pops rest);
      rw_step_send_and_transition c path_subst pi dbs s_and_t
  | Fail                                 ->
      assert (check_only_pops rest);
      fail_out_of_running_or_sending_config (ConfigRealRunning c)
  | Pop                                  -> failure "cannot happen"

let iw_step_send_and_transition_from_ideal_fun (c : config_ideal_running)
    (pi : prover_infos) (dbs : rewriting_dbs) (base : int)
    (fun_sp : symb_pair) (iip : string list) (msg : string)
    (msg_args : form list) (port_form : form option)
    (new_iws : ideal_world_state) : config * eff =
  let (root, _) = fun_sp in
  match port_form with
  | None           ->  (* adversarial message to adversary/simulator *)
      let path = {inter_id_path = root :: iip; msg = msg} in
      let sme =
        SMET_Ord
        {mode           = Adv;
         dir            = Out;
         src_port_form  = make_port_form func_form (int_form 1);
         path           = path;
         args           = msg_args;
         dest_port_form =
           make_port_form adv_addr_form (int_form base)} in
      let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
      (ConfigIdealSending
       {maps = c.maps;
        gc   = c.gc;
        pi   = c.pi;
        dbs  = c.dbs;
        iw   = c.iw;
        ig   = c.ig;
        iws  = new_iws;
        iwsc = IWSC_IdealFunc fun_sp;
        sme  = sme},
       EffOK)
  | Some port_form ->  (* direct message to environment *)
      let (comp, sub) =
        match iip with
        | [comp; sub] -> (comp, sub)
        | _           -> failure "should not happen" in
      let source_pi = get_pi_of_sub_interface c.maps root comp sub in
      let path = {inter_id_path = root :: iip; msg = msg} in
      let sme =
        SMET_Ord
        {mode           = Dir;
         dir            = Out;
         src_port_form  = make_port_form func_form (int_form source_pi);
         path           = path;
         args           = msg_args;
         dest_port_form = port_form} in
      let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
      (ConfigIdealSending
       {maps = c.maps;
        gc   = c.gc;
        pi   = c.pi;
        dbs  = c.dbs;
        iw   = c.iw;
        ig   = c.ig;
        iws  = new_iws;
        iwsc = IWSC_IdealFunc fun_sp;
        sme  = sme},
       EffOK)

let iw_step_send_and_transition_from_sim_basic_adv_left
    (c : config_ideal_running) (pi : prover_infos) (dbs : rewriting_dbs)
    (base : int) (sim_sp : symb_pair) (iip : string list) (msg : string)
    (msg_args : form list) (new_iws : ideal_world_state)
    (i : int) : config * eff =
  let (root, _) = sim_sp in
  let basic =
    match iip with
    | [basic] -> basic
    | _       -> failure "should not happen" in
  let path = {inter_id_path = [root; basic]; msg = msg} in
  let sim_rf_addr =
    addr_concat_form_from_list_smart func_form
    (if i = -1
     then Option.get c.iws.main_sim_state.addr
     else Option.get ((List.nth c.iws.other_sims_states i).addr)) in
  let sme =
    SMET_Ord
    {mode           = Adv;
     dir            = In;
     src_port_form  = make_port_form adv_addr_form (int_form base);
     path           = path;
     args           = msg_args;
     dest_port_form = make_port_form sim_rf_addr (int_form 1)} in
  let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
  (ConfigIdealSending
   {maps = c.maps;
    gc   = c.gc;
    pi   = c.pi;
    dbs  = c.dbs;
    iw   = c.iw;
    ig   = c.ig;
    iws  = new_iws;
    iwsc =
      if i = -1
      then IWSC_MainSim (base, sim_sp)
      else IWSC_OtherSim (base, sim_sp, i);
    sme  = sme},
   EffOK)

let iw_step_send_and_transition_from_sim_comp_adv_right
    (c : config_ideal_running) (pi : prover_infos) (dbs : rewriting_dbs)
    (base : int) (sim_sp : symb_pair) (iip : string list) (msg : string)
    (msg_args : form list) (new_iws : ideal_world_state) (i : int)
      : config * eff =
  let sim_rf_addr =
    if i = -1
    then Option.get c.iws.main_sim_state.addr
    else Option.get ((List.nth c.iws.other_sims_states i).addr) in
  let adv_pis_of_rf_args =
    if i = -1
    then let (_, _, adv_pis, _) = c.iw.iw_main_sim in adv_pis
    else let (_, _, adv_pis, _) = List.nth c.iw.iw_other_sims i in adv_pis in
  let (root, _) = sim_sp in
  let sim_bt = unloc (IdPairMap.find sim_sp c.maps.sim_map) in
  let sim_rf = sim_bt.sims in
  let ft = IdPairMap.find (root, sim_rf) c.maps.fun_map in
  let find_param_or_sub_fun_info (param_or_sub_fun : symbol)
        : int    *  (* index of child - for source address *)
          int    *  (* adv port index - for destination address *)
          symbol    (* root of basic adv interface of param or sub_fun *) =
    if is_param_of_real_fun_tyd ft param_or_sub_fun
      then let child_i =
             index_of_param_of_real_fun_tyd ft param_or_sub_fun in
           let (param_root, _, _) =
             porsf_info_dir_inter_of_param_of_real_fun_tyd ft
             param_or_sub_fun in
           (1 + child_i,
            List.nth adv_pis_of_rf_args child_i,
            param_root)
    else if is_sub_fun_of_real_fun_tyd ft param_or_sub_fun
      then let child_i =
                 sub_fun_ord_of_real_fun_tyd ft param_or_sub_fun in
           let (sf_root, _, _) =
             sub_fun_porsf_info_of_real_fun_tyd ft param_or_sub_fun in
           (1 + num_params_of_real_fun_tyd ft + child_i,
            base + 1 +
            num_adv_pis_of_parties_of_real_fun c.maps root ft +
            child_i,
            sf_root)
    else failure "should not happen" in
  let (rf, mid, sub) =
    match iip with
    | [rf; mid; sub] -> (rf, mid, sub)
    | _              -> failure "should not happen" in
  let () = assert (rf = sim_rf) in
  if id_adv_inter_of_fun_tyd ft = Some mid
  then let comp = mid in
       let porti = get_pi_of_sub_interface c.maps root comp sub in
       let adv_pi = porti + base in
       let path = {inter_id_path = [root; comp; sub]; msg = msg} in
       let sme =
         SMET_Ord
         {mode           = Adv;
          dir            = Out;
          src_port_form  =
            make_port_form
            (addr_concat_form_from_list_smart func_form sim_rf_addr)
            (int_form porti);
          path           = path;
          args           = msg_args;
          dest_port_form = make_port_form adv_addr_form (int_form adv_pi)} in
       let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
       (ConfigIdealSending
        {maps = c.maps;
         gc   = c.gc;
         pi   = c.pi;
         dbs  = c.dbs;
         iw   = c.iw;
         ig   = c.ig;
         iws  = new_iws;
         iwsc =
           if i = -1
           then IWSC_MainSim (base, sim_sp)
           else IWSC_OtherSim (base, sim_sp, i);
         sme  = sme},
        EffOK)
  else let param_or_sub_fun = mid in
       let (child_i, adv_pi, p_or_sf_root) =
         find_param_or_sub_fun_info param_or_sub_fun in
       let path =
         {inter_id_path = p_or_sf_root :: List.drop 2 iip;
          msg = msg} in
       let sme =
         SMET_Ord
         {mode           = Adv;
          dir            = Out;
          src_port_form  =
            make_port_form
            (addr_concat_form_from_list_smart func_form
             (sim_rf_addr @ [child_i]))
            (int_form 1);
          path           = path;
          args           = msg_args;
          dest_port_form = make_port_form adv_addr_form (int_form adv_pi)} in
       let () = check_sme_port_index_consistency c.maps c.gc pi dbs sme in
       (ConfigIdealSending
        {maps = c.maps;
         gc   = c.gc;
         pi   = c.pi;
         dbs  = c.dbs;
         iw   = c.iw;
         ig   = c.ig;
         iws  = new_iws;
         iwsc =
           if i = -1
           then IWSC_MainSim (base, sim_sp)
           else IWSC_OtherSim (base, sim_sp, i);
         sme  = sme},
        EffOK)

let iw_step_send_and_transition_from_sim (c : config_ideal_running)
    (pi : prover_infos) (dbs : rewriting_dbs) (base : int)
    (sim_sp : symb_pair) (iip : string list) (msg : string)
    (msg_args : form list) (port_form : form option)
    (new_iws : ideal_world_state) (i : int) : config * eff =
  match port_form with
  | None ->
      (match List.length iip with
       | 1 ->
           iw_step_send_and_transition_from_sim_basic_adv_left c pi dbs base
           sim_sp iip msg msg_args new_iws i
       | 3 ->
           iw_step_send_and_transition_from_sim_comp_adv_right c pi dbs base
           sim_sp iip msg msg_args new_iws i
       | _ -> failure "cannot happen")
  | Some _ -> failure "cannot happen"

let iw_step_send_and_transition (c : config_ideal_running)
    (path_subst : form -> form) (pi : prover_infos)
    (dbs : rewriting_dbs) (s_and_t : send_and_transition_tyd)
      : config * eff =
  let {msg_expr; state_expr} = s_and_t in
  let {path; args = msg_args; port_expr} = msg_expr in
  let {inter_id_path = iip; msg} = unloc path in
  let msg_args =
    List.map
    (fun arg ->
       lc_apply_and_path_subst LCAM_WeakSimp c.gc c.lc path_subst dbs arg)
    (unloc msg_args) in
  let port_form =
    match port_expr with
    | None      -> None
    | Some expr ->
        let port =
          lc_apply_and_path_subst LCAM_NoSimp c.gc c.lc path_subst dbs expr
        in Some (simplify_port c.gc dbs port) in
  let {UcTypedSpec.id = state_id; UcTypedSpec.args = state_args} =
    state_expr in
  let state_id = unloc state_id and state_args = unloc state_args in
  let state_args =
    List.map
    (fun arg ->
       lc_apply_and_path_subst LCAM_WeakSimp c.gc c.lc path_subst dbs arg)
    state_args in
  let new_state = {id = state_id; args = state_args} in
  let new_iws =
    match c.iwrc with
    | IWRC_IdealFunc _           ->
        {c.iws with ideal_fun_state = new_state}
    | IWRC_MainSim _             ->
        {c.iws with
         main_sim_state =
           update_state_in_sim_state c.iws.main_sim_state new_state}
    | IWRC_OtherSim (_, _, _, i) ->
        {c.iws with
         other_sims_states =
           List.modify_at i
           (fun ss -> update_state_in_sim_state ss new_state)
           c.iws.other_sims_states} in
  match c.iwrc with
  | IWRC_IdealFunc (base, fun_sp, _)   ->
      iw_step_send_and_transition_from_ideal_fun c pi dbs base fun_sp
      iip msg msg_args port_form new_iws
  | IWRC_MainSim (base, sim_sp, _)     ->
      iw_step_send_and_transition_from_sim c pi dbs base sim_sp
      iip msg msg_args port_form new_iws (-1)
  | IWRC_OtherSim (base, sim_sp, _, i) ->
      iw_step_send_and_transition_from_sim c pi dbs base sim_sp
      iip msg msg_args port_form new_iws i

let step_ideal_running_config (c : config_ideal_running) (pi : prover_infos)
    (dbs : rewriting_dbs) : config * eff =
  let rec handle_pops (rest : instr_interp list) (lc : local_context)
        : instr_interp list * local_context =
    (assert (not (List.is_empty rest));
     if unloc (List.hd rest) = Pop
     then handle_pops (List.tl rest) (lc_pop lc)
     else (rest, lc)) in
  let rec check_only_pops (rest : instr_interp list) : bool =
    match rest with
    | []            -> true
    | instr :: rest -> unloc instr = Pop && check_only_pops rest in
  let inss = c.ins in
  assert (not (List.is_empty inss));
  let (next, rest) = (List.hd inss, List.tl inss) in
  let path_subst : form -> form =
    let root = root_of_ideal_world_running_context c.iwrc in
    cond_subst_path_prefix_in_form ["Top"; "UC___" ^ root] c.path in
  match unloc next with
  | Assign (lhs, expr)                   ->
      let lc = step_assign c.gc c.lc path_subst dbs lhs expr in
      let (rest, lc) = handle_pops rest lc in
      (ConfigIdealRunning {c with lc = lc; ins = rest},
       EffOK)
  | Sample (lhs, expr)                   ->
      let (gc, lc, id) = step_sample c.gc c.lc path_subst dbs lhs expr in
      let (rest, lc) = handle_pops rest lc in
      (ConfigIdealRunning {c with gc = gc; lc = lc; ins = rest},
       EffRand id)
  | ITE (expr, inss_then, inss_else_opt) ->
      let inss =
        step_if_then_else c.gc c.lc path_subst pi dbs
        expr inss_then inss_else_opt in
      let (rest, _) = handle_pops (inss @ rest) c.lc in
      (ConfigIdealRunning {c with ins = rest}, EffOK)
  | Match (expr, clauses)                ->
      let (lc, inss) = step_match c.gc c.lc path_subst pi dbs expr clauses in
      let (rest, _) = handle_pops (inss @ rest) lc in
      (ConfigIdealRunning {c with lc = lc; ins = rest},
       EffOK)
  | SendAndTransition s_and_t            ->
      assert (check_only_pops rest);
      iw_step_send_and_transition c path_subst pi dbs s_and_t
  | Fail                                 ->
      assert (check_only_pops rest);
      fail_out_of_running_or_sending_config (ConfigIdealRunning c)
  | Pop                                  -> failure "cannot happen"

(* should only be called with ordinary sme that will successfully
   match *)

let match_ord_sme_against_msg_match_clauses
    (clauses : msg_match_clause_tyd list) (sme : sent_msg_expr_ord_tyd)
      : ((EcIdent.t * ty) * form) list * instruction_tyd list located =
  let rec match_sme clauses =
    match clauses with
    | []                -> failure "should not happen"
    | clause :: clauses ->
        let {msg_pat; code} = clause in
        let msg_path_pat = msg_pat.msg_path_pat in
        let {inter_id_path; msg_or_star} = unloc msg_path_pat in
        match msg_or_star with
        | MsgOrStarMsg msg ->
           if sme.path.inter_id_path = inter_id_path &&
              sme.path.msg = msg
           then (match_msg_pat msg_pat sme.src_port_form sme.args, code)
           else match_sme clauses
        | MsgOrStarStar    ->
            if UcUtils.sl1_starts_with_sl2 sme.path.inter_id_path
               inter_id_path
            then ([], code)  (* code will be fail *)
            else match_sme clauses in
  match_sme clauses

(* should only be called with ordinary sme that will successfully
   match *)

let match_ord_sme_in_state (is_sim : bool) (addr : form)
    (sbt : state_body_tyd) (state_args : form list)
    (sme : sent_msg_expr_ord_tyd)
      : local_context * instruction_tyd list located =
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
    List.map (fun ((id, _), f) -> (LCB_Bound (id, f))) mm_binds in
  let envport_maybe =
    if is_sim then [] else [LCB_EnvPort addr] in
  let internal_ports =
    List.mapi
    (fun i (_, id) -> LCB_IntPort (id, port_of_addr (i + 1)))
    (QidMap.bindings sbt.internal_ports) in
  (* when internal ports are turned into port indices (beginning at 1),
     we use the ordering List.compare String.compare; this is stable
     under the prepending of RealFun, so that [Party] in the real
     functionality and [RealFun; Party] in its simulator will be
     assigned the same port index *)
  let lc =
    lc_create
    (state_params   @
     vars           @
     mm_binds       @
     envport_maybe  @
     internal_ports
    ) in
   (lc, mm_instructs)

let from_adv_to_func_find_rel_addr_adv_pi_func_sp
    (gc : global_context) (pi : prover_infos) (dbs : rewriting_dbs)
    (maps : maps_tyd) (dest_port : form) (rw : real_world)
      : (int list * int * symb_pair * path) option =
  let dest_addr = port_to_addr_form dest_port in

  let try_sub_funs (sp : symb_pair) (path : path) (rel : int list)
      (base : int) (nargs : int) : (int list * int * symb_pair * path) option =
    let ft = IdPairMap.find sp maps.fun_map in
    let num_sub_funs = num_sub_funs_of_real_fun_tyd ft in
    let rec try_sf (i : int) : (int list * int * symb_pair * path) option =
      let rel_nargs_i = rel @ [nargs + i] in
      if i > num_sub_funs
        then None
      else if eval_bool_form_to_bool gc pi dbs
              (f_eq
               (addr_concat_form_from_list_smart func_form rel_nargs_i)
               dest_addr)
        then let (root, id, clone) =
               sub_fun_porsf_info_nth_of_real_fun_tyd ft (i - 1) in
             Some
             (rel_nargs_i,
              get_adv_pi_of_nth_sub_fun_of_real_fun maps
              (fst sp) base ft (i - 1),
              (root, id),
              path @ [clone])
      else try_sf (i + 1) in
    try_sf 1 in

  let rec find ((sp, adv_pi, path, rwas) : real_world) (rel : int list)
        : (int list * int * symb_pair * path) option =
    if eval_bool_form_to_bool gc pi dbs
       (f_eq (addr_concat_form_from_list_smart func_form rel) dest_addr)
    then Some (rel, adv_pi, sp, path)
    else let nargs = List.length rwas in
         let rec loop_args i =
           if i > nargs
             then try_sub_funs sp path rel adv_pi nargs
           else let rel_i = rel @ [i] in
                let addr_i =
                  addr_concat_form_from_list_smart func_form rel_i in
                if eval_bool_form_to_bool gc pi dbs
                   (addr_le_form addr_i dest_addr)
                then match List.nth rwas (i - 1) with
                     | RWA_Real rw                  -> find rw (rel @ [i])
                     | RWA_Ideal (sp, adv_pi, path) ->
                         if eval_bool_form_to_bool gc pi dbs
                            (f_eq addr_i dest_addr)
                         then Some (rel_i, adv_pi, sp, path)
                         else None
                else loop_args (i + 1) in
         loop_args 1
  in match try_destr_port_as_func_rel dest_port with
     | None          -> find rw []
     | Some (rel, _) ->
         match select_real_world maps rw rel with
         | None                    -> None
         | Some (sp, adv_pi, path) -> Some (rel, adv_pi, sp, path)

(* indices in the following are from 0 *)

type real_world_rel_select =
  | RW_Select_RealFun     of symb_pair * path * int * real_world_arg list *
                             (symb_pair *  (* if arg: parent *)
                              path      *  (* parent's path *)
                              int       *  (* index into parent's args *)
                              int) option  (* parent's adv pi *)
  | RW_Select_IdealFunArg of symb_pair * path * int *
                             symb_pair *   (* parent *)
                             path      *   (* parent's path *)
                             int       *   (* index into parent's args *)
                             int           (* parent's adv pi *)
  | RW_Select_IdealSubFun of symb_pair * path * int *
                             symb_pair *   (* parent *)
                             path      *   (* parent's path *)
                             int       *   (* index into parent's sub funs *)
                             int           (* parent's adv pi *)

let select_rel_addr_of_real_world
    (maps : maps_tyd) (rel : int list) (rw : real_world)
      : real_world_rel_select =
  let rec sel (rel : int list) ((sp, base, path, rwas) : real_world)
      (par_opt : (symb_pair * path * int * int) option) =
    match rel with
    | []       -> Some (RW_Select_RealFun (sp, path, base, rwas, par_opt))
    | i :: rel ->  (* i starts at 1 *)
        let nargs = List.length rwas in
        if i <= 0
          then None
        else if i <= nargs
          then (match List.nth rwas (i - 1) with
                | RWA_Real rw                      ->
                    sel rel rw (Some (sp, path, i - 1, base))
                | RWA_Ideal (sp_arg, advpi, path_arg) ->
                    Some
                    (RW_Select_IdealFunArg
                     (sp_arg, path_arg, advpi, sp, path, i - 1, base)))
        else let ft = IdPairMap.find sp maps.fun_map in
             let (root, _) = sp in
             let num_sub_funs = num_sub_funs_of_real_fun_tyd ft in
             let j = i - nargs in
             if j <= num_sub_funs
             then let (sf_root, id, clone) =
                    sub_fun_porsf_info_nth_of_real_fun_tyd ft (j - 1) in
                  Some
                  (RW_Select_IdealSubFun
                   ((sf_root, id),
                    path @ [clone],
                    get_adv_pi_of_nth_sub_fun_of_real_fun maps
                    root base ft (j - 1),
                    sp, path, j - 1, base))
             else None
  in match sel rel rw None with
     | None      -> failure "should not happen"
     | Some rwrs -> rwrs

let step_real_sending_config (c : config_real_sending) (pi : prover_infos)
    (dbs : rewriting_dbs) : config * eff =
  let mode = mode_of_sent_msg_expr_tyd c.sme in
  let dest_port = dest_port_of_sent_msg_expr_tyd c.sme in
  let source_port = source_port_of_sent_msg_expr_tyd c.sme in

  let direct_real_func_party_match (rel : int list) (base : int)
      (func_sp : symb_pair) (path : path) (party_id : symbol)
      (comp : symbol) (sub : symbol) (state_id : symbol)
      (state_args : form list) (sbt : state_body_tyd) : config * eff =
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, _) = func_sp in
        let iip = sme_ord.path.inter_id_path in
        let addr = addr_concat_form_from_list_smart func_form rel in
        if List.take 2 iip = [root; comp] && sme_ord.dir = In
        then (assert (List.length iip = 3 && List.nth iip 2 = sub);
              let sme_ord =
                drop_head_of_msg_path_in_sent_msg_expr_ord_tyd sme_ord in
              let (lc, ins) =
                match_ord_sme_in_state false addr sbt state_args
                sme_ord in
              (ConfigRealRunning
               {maps = c.maps;
                gc   = c.gc;
                pi   = c.pi;
                dbs  = c.dbs;
                rw   = c.rw;
                ig   = c.ig;
                rws  = c.rws;
                rwrc = RWRC_RealFunc (rel, base, func_sp, party_id, state_id);
                path = path;
                lc   = lc;
                ins  = create_instr_interp_list ins},
               EffOK))
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
            pp_rel_addr_real_func_info (rel, func_sp, party_id));
         fail_out_of_running_or_sending_config (ConfigRealSending c)) in

  let direct_real_func_find_party (rfi : real_fun_info)
        : (symbol * symbol * symbol) option =
    let rec find (bndgs : (symbol * party_info) list)
          : (symbol * symbol * symbol) option =
      match bndgs with
      | []                          -> None
      | (pty_id, pty_info) :: bndgs ->
          match pty_info.pi_pdi with
          | None                   -> find bndgs
          | Some (comp, sub, pind) ->
              if equal_port_index_of_port c.gc pi dbs dest_port pind
              then Some (pty_id, comp, sub)
              else find bndgs
    in find (IdMap.bindings rfi) in

  let from_env () =
    if mode = Dir &&
       equal_func_rel_addr_of_port c.gc pi dbs dest_port [] &&
       eval_bool_form_to_bool c.gc pi dbs
       (envport_form func_form source_port)
      then let (func_sp, base, path, _) = c.rw in
           let (root, _) = func_sp in
           let ft = IdPairMap.find func_sp c.maps.fun_map in
           let rfi = get_info_of_real_func c.maps root base ft in
           match direct_real_func_find_party rfi with
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
               direct_real_func_party_match [] base func_sp path pid comp sub
               state_id state_args sbt
    else if mode = Adv &&
            equal_adv_addr_of_port c.gc pi dbs dest_port &&
            ((equal_port_index_of_port c.gc pi dbs dest_port 0 &&
              equal_env_root_port c.gc pi dbs source_port) ||
             (greater_than_or_equal_port_index_of_port c.gc pi dbs
              dest_port c.ig &&
              eval_bool_form_to_bool c.gc pi dbs
              (envport_form func_form source_port)))
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
              if equal_port_index_of_port c.gc pi dbs dest_port pind
              then if equal_port_index_of_port c.gc pi dbs source_port adv_pi
                   then Some (pty_id, comp, sub)
                   else None
              else find bndgs
    in find (IdMap.bindings rfi) in

  let from_adv_to_real_func_party_match (rel : int list) (base : int)
      (func_sp : symb_pair) (path : path) (party_id : symbol)
      (comp : symbol) (sub : symbol) (state_id : symbol)
      (state_args : form list) (sbt : state_body_tyd) : config * eff =
    match c.sme with
    | SMET_Ord sme_ord        ->
        let (root, _) = func_sp in
        let iip = sme_ord.path.inter_id_path in
        let addr = addr_concat_form_from_list_smart func_form rel in
        if List.take 2 iip = [root; comp] && sme_ord.dir = In
        then (assert (List.length iip = 3 && List.nth iip 2 = sub);
              if sbt.is_initial
              then (debugging_message
                    (fun ppf ->
                       fprintf ppf
                       ("@[adversarial@ message@ rejected@ in@ initial@ " ^^
                        "state@ at@ %a@]")
                       pp_rel_addr_real_func_info (rel, func_sp, party_id));
                    fail_out_of_running_or_sending_config
                    (ConfigRealSending c))
              else let sme_ord =
                     drop_head_of_msg_path_in_sent_msg_expr_ord_tyd sme_ord in
                   let (lc, ins) =
                     match_ord_sme_in_state false addr sbt state_args
                     sme_ord in
                   (ConfigRealRunning
                    {maps = c.maps;
                     gc   = c.gc;
                     pi   = c.pi;
                     dbs  = c.dbs;
                     rw   = c.rw;
                     ig   = c.ig;
                     rws  = c.rws;
                     rwrc =
                       RWRC_RealFunc (rel, base, func_sp, party_id, state_id);
                     path = path;
                     lc   = lc;
                     ins  = create_instr_interp_list ins},
                    EffOK))
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
      (func_sp : symb_pair) (path : path) : config * eff =
    let (root, _) = func_sp in
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
        from_adv_to_real_func_party_match rel base func_sp path ptyid comp sub
        state_id state_args sbt in

  let from_adv_to_ideal_func (rel : int list) (adv_pi : int)
      (func_sp : symb_pair) (path : path) (ifbt : ideal_fun_body_tyd)
        : config * eff =
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, _) = func_sp in
        let basic_opt = ifbt.id_adv_inter in
        let {id = state_id; args = state_args} =
          ideal_state_of_fun_state (ILMap.find rel c.rws) in
        let sbt = unloc (IdMap.find state_id ifbt.states) in
        let iip = sme_ord.path.inter_id_path in
        let addr = addr_concat_form_from_list_smart func_form rel in
        if basic_opt <> None && iip = [root; Option.get basic_opt] &&
           sme_ord.dir = In &&
           equal_port_index_of_port c.gc pi dbs dest_port 1 &&
           equal_port_index_of_port c.gc pi dbs source_port adv_pi
        then if sbt.is_initial
             then (debugging_message
                   (fun ppf ->
                      fprintf ppf
                      ("@[adversarial@ message@ rejected@ in@ initial@ " ^^
                       "state@ at@ %a@]")
                      pp_rel_addr_ideal_func_info (rel, func_sp));
                   fail_out_of_running_or_sending_config
                   (ConfigRealSending c))
             else let sme_ord =
                    drop_head_of_msg_path_in_sent_msg_expr_ord_tyd sme_ord in
                  let (lc, ins) =
                    match_ord_sme_in_state false addr sbt state_args
                    sme_ord in
                  (ConfigRealRunning
                   {maps = c.maps;
                    gc   = c.gc;
                    pi   = c.pi;
                    dbs  = c.dbs;
                    rw   = c.rw;
                    ig   = c.ig;
                    rws  = c.rws;
                    rwrc = RWRC_IdealFunc (rel, adv_pi, func_sp, state_id);
                    path = path;
                    lc   = lc;
                    ins  = create_instr_interp_list ins},
                   EffOK)
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

  let from_adv_to_func () : config * eff =
    match from_adv_to_func_find_rel_addr_adv_pi_func_sp
          c.gc pi dbs c.maps dest_port c.rw with
    | None                              ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            "@[bad@ destination@ address@ for@ real@ world@]");
        fail_out_of_running_or_sending_config (ConfigRealSending c))
    | Some (rel, adv_pi, func_sp, path) ->
        let fbt = unloc (IdPairMap.find func_sp c.maps.fun_map) in
        match fbt with
        | FunBodyRealTyd _     -> from_adv_to_real_func rel adv_pi func_sp path
        | FunBodyIdealTyd ifbt ->
            from_adv_to_ideal_func rel adv_pi func_sp path ifbt in

  let from_adv () =
    if mode = Dir ||
       greater_than_or_equal_adv_addr_of_port c.gc pi dbs dest_port ||
       not (equal_adv_addr_of_port c.gc pi dbs source_port) ||
       less_than_port_index_of_port c.gc pi dbs source_port 0
      then fail_out_of_running_or_sending_config (ConfigRealSending c)
    else if greater_than_or_equal_func_rel_addr_of_port c.gc pi dbs
            dest_port []
      then if equal_port_index_of_port c.gc pi dbs source_port 0
           then fail_out_of_running_or_sending_config (ConfigRealSending c)
           else from_adv_to_func ()
    else if equal_port_index_of_port c.gc pi dbs source_port 0 =
            equal_env_root_port c.gc pi dbs dest_port
      then msg_out_of_sending_config (ConfigRealSending c) CtrlEnv
    else fail_out_of_running_or_sending_config (ConfigRealSending c) in

  let from_parent_to_real_func (rel : int list) (base : int)
      (func_sp : symb_pair) (path : path) : config * eff =
    let (root, _) = func_sp in
    let ft = IdPairMap.find func_sp c.maps.fun_map in
    let rfi = get_info_of_real_func c.maps root base ft in
    match direct_real_func_find_party rfi with
    | None                  ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            ("@[unable@ to@ find@ party@ accepting@ " ^^
             "destination@ port@ id@]"));
        fail_out_of_running_or_sending_config (ConfigRealSending c))
    | Some (pid, comp, sub) ->
        let pbt = unloc (party_of_real_fun_tyd ft pid) in
        let rs = real_state_of_fun_state (ILMap.find rel c.rws) in
        let {id = state_id; args = state_args} = IdMap.find pid rs in
        let sbt = unloc (IdMap.find state_id pbt.states) in
        direct_real_func_party_match rel base func_sp path pid comp sub
        state_id state_args sbt in

  let from_parent_to_ideal_func (rel : int list) (adv_pi : int)
      (func_sp : symb_pair) (path : path) (ifbt : ideal_fun_body_tyd)
        : config * eff =
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, _) = func_sp in
        let comp = ifbt.id_dir_inter in
        let {id = state_id; args = state_args} =
          ideal_state_of_fun_state (ILMap.find rel c.rws) in
        let sbt = unloc (IdMap.find state_id ifbt.states) in
        let addr = addr_concat_form_from_list_smart func_form rel in
        (match sme_ord.path.inter_id_path with
         | [root'; comp'; sub'] ->
             (assert
              (root' = root && comp' = comp && sme_ord.dir = In &&
               check_sub_interface_and_get_pi c.maps root comp sub' <> None);
              let sme_ord =
                drop_head_of_msg_path_in_sent_msg_expr_ord_tyd sme_ord in
              let (lc, ins) =
                match_ord_sme_in_state false addr sbt state_args
                sme_ord in
              (ConfigRealRunning
               {maps = c.maps;
                gc   = c.gc;
                pi   = c.pi;
                dbs  = c.dbs;
                rw   = c.rw;
                ig   = c.ig;
                rws  = c.rws;
                rwrc = RWRC_IdealFunc (rel, adv_pi, func_sp, state_id);
                path = path;
                lc   = lc;
                ins  = create_instr_interp_list ins},
               EffOK))
         | _                    -> failure "should not happen")
    | SMET_EnvAdv _    ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            "@[message@ match@ failure@ at@ %a@]"
            pp_rel_addr_ideal_func_info (rel, func_sp));
         fail_out_of_running_or_sending_config (ConfigRealSending c)) in

  let from_parent_to_arg_or_sub_fun (rel : int list) (sp_par : symb_pair)
      (path : path) (base : int) (rwas : real_world_arg list)
        : config * eff =
    let num_args = List.length rwas in
    let ft_par = IdPairMap.find sp_par c.maps.fun_map in
    let num_sub_funs = num_sub_funs_of_real_fun_tyd ft_par in
    let arg_or_sf_ind =
      match try_destr_port_as_func_rel dest_port with
      | None               -> failure "cannot happen"
      | Some (dest_rel, _) ->
          if List.length dest_rel <> List.length rel + 1
          then failure "cannot happen"
          else List.last dest_rel in
    if arg_or_sf_ind < 1 ||
       arg_or_sf_ind > num_args + num_sub_funs
      then failure "cannot happen"
    else if arg_or_sf_ind <= num_args
      then match List.nth rwas (arg_or_sf_ind - 1) with
           | RWA_Real (sp, adv_pi, path, _) ->
               from_parent_to_real_func (rel @ [arg_or_sf_ind]) adv_pi sp path
           | RWA_Ideal (sp, adv_pi, path)   ->
               let fbt = unloc (IdPairMap.find sp c.maps.fun_map) in
               let ifbt = ideal_fun_body_tyd_of fbt in
               from_parent_to_ideal_func (rel @ [arg_or_sf_ind]) adv_pi sp
               path ifbt
    else let sf_ind = arg_or_sf_ind - num_args - 1 in  (* from 0 *)
         let (root, id, clone) =
           sub_fun_porsf_info_nth_of_real_fun_tyd ft_par sf_ind in
         let sp = (root, id) in
         let fbt = unloc (IdPairMap.find sp c.maps.fun_map) in
         let ifbt = ideal_fun_body_tyd_of fbt in
         from_parent_to_ideal_func (rel @ [arg_or_sf_ind])
         (get_adv_pi_of_nth_sub_fun_of_real_fun c.maps
          (fst sp_par) base ft_par sf_ind)
         sp (path @ [clone]) ifbt in

  let internal_real_func_find_party (rfi : real_fun_info) : symbol option =
    let rec find (bndgs : (symbol * party_info) list) : symbol option =
      match bndgs with
      | []                          -> None
      | (pty_id, pty_info) :: bndgs ->
          let intpi = pty_info.pi_ipi in
          if equal_port_index_of_port c.gc pi dbs dest_port intpi
          then Some pty_id
          else find bndgs
    in find (IdMap.bindings rfi) in

  let internal_real_func_party_match (rel : int list) (base : int)
      (func_sp : symb_pair) (path : path) (party_id : symbol)
      (state_id : symbol) (state_args : form list) (sbt : state_body_tyd)
      (param_or_sub_fun_name : symbol) (id_dir : symbol)
        : config * eff =
    let addr = addr_concat_form_from_list_smart func_form rel in
    match c.sme with
    | SMET_Ord sme_ord ->
        let sme_ord =
          match subst_comp_and_drop_root_in_sent_msg_expr_ord_tyd sme_ord
                id_dir param_or_sub_fun_name with
          | None     -> failure "should not happen"
          | Some sme -> sme in
        (assert (sme_ord.dir = Out);
         let (lc, ins) =
           match_ord_sme_in_state false addr sbt state_args sme_ord in
         (ConfigRealRunning
          {maps = c.maps;
           gc   = c.gc;
           pi   = c.pi;
           dbs  = c.dbs;
           rw   = c.rw;
           ig   = c.ig;
           rws  = c.rws;
           rwrc = RWRC_RealFunc (rel, base, func_sp, party_id, state_id);
           path = path;
           lc   = lc;
           ins  = create_instr_interp_list ins},
          EffOK))
    | SMET_EnvAdv _    ->
        (debugging_message
         (fun ppf ->
            fprintf ppf
            "@[message@ match@ failure@ at@ %a@]"
            pp_rel_addr_real_func_info (rel, func_sp, party_id));
         fail_out_of_running_or_sending_config (ConfigRealSending c)) in

  let from_arg_or_sub_fun_to_parent_cont (rel : int list) (func_sp : symb_pair)
      (path : path) (base : int) (param_or_subfun_name : symbol)
      (id_dir : symbol) : config * eff =
    let (root, _) = func_sp in
    let ft = IdPairMap.find func_sp c.maps.fun_map in
    let rfi = get_info_of_real_func c.maps root base ft in
    let rel = List.take (List.length rel - 1) rel in
    if not (equal_func_rel_addr_of_port c.gc pi dbs dest_port rel)
    then (debugging_message
          (fun ppf ->
             fprintf ppf
             "@[destination@ address@ not@ address@ of@ parent@]");
          fail_out_of_running_or_sending_config (ConfigRealSending c))
    else match internal_real_func_find_party rfi with
         | None     ->
             (debugging_message
              (fun ppf ->
                 fprintf ppf
                 ("@[unable@ to@ find@ party@ with@ correct@ " ^^
                  "internal@ port@ id@]"));
             fail_out_of_running_or_sending_config (ConfigRealSending c))
         | Some pid ->
             let pbt = unloc (party_of_real_fun_tyd ft pid) in
             let rs = real_state_of_fun_state (ILMap.find rel c.rws) in
             let {id = state_id; args = state_args} = IdMap.find pid rs in
             let sbt = unloc (IdMap.find state_id pbt.states) in
             internal_real_func_party_match rel base func_sp path pid
             state_id state_args sbt param_or_subfun_name id_dir in

  let from_func_to_env_or_parent (rel : int list)
      (rwrs : real_world_rel_select) : config * eff =
    match rwrs with
    | RW_Select_RealFun (sp, _, _, _, par_opt)            ->
        (match par_opt with
         | None                                         ->  (* to env *)
             let sme = c.sme in
             let dest_port = dest_port_of_sent_msg_expr_tyd sme in
             if try eval_bool_form_to_bool c.gc pi dbs
                    (envport_form
                     (addr_concat_form_from_list_smart func_form rel)
                     dest_port) with
                | ECProofEngine -> raise StepBlockedPortOrAddrCompare
             then msg_out_of_sending_config (ConfigRealSending c) CtrlEnv
             else (debugging_message
                   (fun ppf ->
                      fprintf ppf
                      "@[envport@ failure@ of@ destination@ port@ at@ %a@]"
                      pp_rel_addr_ideal_func_info (rel, sp));
                   fail_out_of_running_or_sending_config (ConfigRealSending c))
         | Some (sp_par, path_par, par_arg_i, par_base) ->
             let ft = IdPairMap.find sp c.maps.fun_map in
             let id_dir = id_dir_inter_of_fun_tyd ft in
             let ft_par = IdPairMap.find sp_par c.maps.fun_map in
             let param_name = param_name_nth_of_real_fun_tyd ft_par par_arg_i in
             from_arg_or_sub_fun_to_parent_cont rel sp_par path_par par_base
             param_name id_dir)
    | RW_Select_IdealFunArg
      (sp, _, _, sp_par, path_par, par_arg_i, par_adv_pi) ->
        let ft = IdPairMap.find sp c.maps.fun_map in
        let id_dir = id_dir_inter_of_fun_tyd ft in
        let ft_par = IdPairMap.find sp_par c.maps.fun_map in
        let param_name = param_name_nth_of_real_fun_tyd ft_par par_arg_i in
        from_arg_or_sub_fun_to_parent_cont rel sp_par path_par par_adv_pi
        param_name id_dir
    | RW_Select_IdealSubFun
      (sp, _, _, sp_par, path_par, par_sf_i, par_adv_pi)  ->
        let ft = IdPairMap.find sp c.maps.fun_map in
        let id_dir = id_dir_inter_of_fun_tyd ft in
        let ft_par = IdPairMap.find sp_par c.maps.fun_map in
        let sf_name = sub_fun_name_nth_of_real_fun_tyd ft_par par_sf_i in
        from_arg_or_sub_fun_to_parent_cont rel sp_par path_par par_adv_pi
        sf_name id_dir in

  let from_func (rel : int list) : config * eff =
    if mode = Adv
    then msg_out_of_sending_config (ConfigRealSending c) CtrlAdv
    else let rwrs = select_rel_addr_of_real_world c.maps rel c.rw in
         if greater_than_func_rel_addr_of_port c.gc pi dbs dest_port rel
         then (match rwrs with
               | RW_Select_RealFun (sp, path, base, rwas, _) ->
                   from_parent_to_arg_or_sub_fun rel sp path base rwas
               | _                                     ->
                   fail_out_of_running_or_sending_config
                   (ConfigRealSending c))
         else from_func_to_env_or_parent rel rwrs in

  try
    match c.rwsc with
    | RWSC_Env           -> from_env ()
    | RWSC_Adv           -> from_adv ()
    | RWSC_Func (rel, _) -> from_func rel
  with
  | ECProofEngine -> raise StepBlockedPortOrAddrCompare

let step_ideal_sending_config (c : config_ideal_sending) (pi : prover_infos)
    (dbs : rewriting_dbs) : config * eff =
  let mode = mode_of_sent_msg_expr_tyd c.sme in
  let dest_port = dest_port_of_sent_msg_expr_tyd c.sme in
  let source_port = source_port_of_sent_msg_expr_tyd c.sme in

  let from_env_to_ideal_fun (func_sp : symb_pair) (path : path) (base : int)
      (ifbt : ideal_fun_body_tyd) : config * eff =
    let msg_match_fail () : config * eff =
      (debugging_message
       (fun ppf ->
          fprintf ppf
          "@[message@ match@ failure@ at@ ideal@ functionality@ %a@]"
          pp_symb_pair func_sp);
       fail_out_of_running_or_sending_config (ConfigIdealSending c)) in
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, _) = func_sp in
        let comp = ifbt.id_dir_inter in
        let {id = state_id; args = state_args} = c.iws.ideal_fun_state in
        let sbt = unloc (IdMap.find state_id ifbt.states) in
        (match sme_ord.path.inter_id_path with
         | [root'; comp'; sub'] ->
              if root' = root && comp' = comp && sme_ord.dir = In
              then (assert
                    (check_sub_interface_and_get_pi c.maps root comp sub' <>
                     None);
                    let sme_ord =
                      drop_head_of_msg_path_in_sent_msg_expr_ord_tyd sme_ord in
                    let (lc, ins) =
                      match_ord_sme_in_state false func_form
                      sbt state_args sme_ord in
                    (ConfigIdealRunning
                     {maps = c.maps;
                      gc   = c.gc;
                      pi   = c.pi;
                      dbs  = c.dbs;
                      iw   = c.iw;
                      ig   = c.ig;
                      iws  = c.iws;
                      iwrc = IWRC_IdealFunc (base, func_sp, state_id);
                      path = path;
                      lc   = lc;
                      ins  = create_instr_interp_list ins},
                     EffOK))
              else msg_match_fail ()
         | _                    -> msg_match_fail ())
    | SMET_EnvAdv _    -> msg_match_fail () in

  let from_env () =
    if mode = Dir &&
       equal_func_rel_addr_of_port c.gc pi dbs dest_port [] &&
       eval_bool_form_to_bool c.gc pi dbs
       (envport_form func_form source_port)
      then let (func_sp, base, path) = c.iw.iw_ideal_func in
           let ft = unloc (IdPairMap.find func_sp c.maps.fun_map) in
           let ifbt = ideal_fun_body_tyd_of ft in
           from_env_to_ideal_fun func_sp path base ifbt
    else if mode = Adv &&
            equal_adv_addr_of_port c.gc pi dbs dest_port &&
            ((equal_port_index_of_port c.gc pi dbs dest_port 0 &&
              equal_env_root_port c.gc pi dbs source_port) ||
             (greater_than_or_equal_port_index_of_port c.gc pi dbs
              dest_port c.ig &&
              eval_bool_form_to_bool c.gc pi dbs
              (envport_form func_form source_port)))
      then msg_out_of_sending_config (ConfigIdealSending c) CtrlAdv
    else fail_out_of_running_or_sending_config (ConfigIdealSending c) in

  let from_adv_or_sim_to_ideal_fun (func_sp : symb_pair) (path : path)
      (base : int) (ifbt : ideal_fun_body_tyd) : config * eff =
    let msg_match_fail () : config * eff =
      (debugging_message
       (fun ppf ->
          fprintf ppf
          "@[message@ match@ failure@ at@ ideal@ functionality@ %a@]"
          pp_symb_pair func_sp);
       fail_out_of_running_or_sending_config (ConfigIdealSending c)) in
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, _) = func_sp in
        let basic_opt = ifbt.id_adv_inter in
        let {id = state_id; args = state_args} = c.iws.ideal_fun_state in
        let sbt = unloc (IdMap.find state_id ifbt.states) in
        (match sme_ord.path.inter_id_path with
         | [root'; basic'] ->
             assert (basic_opt <> None);
             if root' = root && basic' = Option.get basic_opt &&
                sme_ord.dir = In
             then if sbt.is_initial
                  then (debugging_message
                        (fun ppf ->
                           fprintf ppf
                           ("@[adversarial@ message@ rejected@ in@ initial@ " ^^
                            "state@ at@ %a@]")
                           pp_symb_pair func_sp);
                        fail_out_of_running_or_sending_config
                        (ConfigIdealSending c))
                  else let sme_ord =
                         drop_head_of_msg_path_in_sent_msg_expr_ord_tyd
                         sme_ord in
                       let (lc, ins) =
                         match_ord_sme_in_state false func_form
                         sbt state_args sme_ord in
                       (ConfigIdealRunning
                        {maps = c.maps;
                         gc   = c.gc;
                         pi   = c.pi;
                         dbs  = c.dbs;
                         iw   = c.iw;
                         ig   = c.ig;
                         iws  = c.iws;
                         iwrc = IWRC_IdealFunc (base, func_sp, state_id);
                         path = path;
                         lc   = lc;
                         ins  = create_instr_interp_list ins},
                        EffOK)
             else msg_match_fail ()
         | _               -> msg_match_fail ())
    | SMET_EnvAdv _    -> msg_match_fail () in

  (* -1 <= i <= List.length c.iw_other_sims - 1

     i is starting point of search, and -1 means the main simulator

     only for use when message's destination address is >= func_addr *)

  let rec find_sim_from_right (i : int)
        : (int * symb_pair * path * int * int list * sim_state) option =
    if i = -1
    then match c.iws.main_sim_state.addr with
         | None      -> None
         | Some addr ->
             if greater_than_or_equal_func_rel_addr_of_port c.gc pi dbs
                dest_port addr
             then let (sp, adv_pi, rf_arg_adv_pis, path) = c.iw.iw_main_sim in
                  let sim_st = c.iws.main_sim_state in
                  Some (i, sp, path, adv_pi, rf_arg_adv_pis, sim_st)
             else None
    else match (List.nth c.iws.other_sims_states i).addr with
         | None      -> find_sim_from_right (i - 1)
         | Some addr ->
             if greater_than_or_equal_func_rel_addr_of_port c.gc pi dbs
                dest_port addr
             then let (sp, adv_pi, rf_arg_adv_pis, path) =
                    List.nth c.iw.iw_other_sims i in
                  let sim_st = List.nth c.iws.other_sims_states i in
                  Some (i, sp, path, adv_pi, rf_arg_adv_pis, sim_st)
             else find_sim_from_right (i - 1) in

  (* -1 <= i <= List.length c.iw_other_sims - 1

     i is starting point of search, and -1 means the main simulator

     only for use when message's destination address is >= func_addr *)

  let rec find_sim_from_left (i : int) (dest_pi : int)
        : (int * symb_pair * path * int * int list * sim_state) option =
    if i = -1
      then let (_, adv_pi, _, _) = c.iw.iw_main_sim in
           if dest_pi = adv_pi
           then let (sp, adv_pi, rf_arg_adv_pis, path) = c.iw.iw_main_sim in
                let sim_st = c.iws.main_sim_state in
                Some (i, sp, path, adv_pi, rf_arg_adv_pis, sim_st)
           else find_sim_from_left (i + 1) dest_pi
    else if i <= List.length c.iw.iw_other_sims - 1
      then let (sp, adv_pi, rf_arg_adv_pis, path) =
             List.nth c.iw.iw_other_sims i in
           if dest_pi = adv_pi
           then let sim_st = List.nth c.iws.other_sims_states i in
                Some (i, sp, path, adv_pi, rf_arg_adv_pis, sim_st)
           else find_sim_from_left (i + 1) dest_pi
    else None in

  let dest_adv_to_sim (i : int) (sim_sp : symb_pair) (sim_path : path)
      (base : int) (sim_rf_addr : int list option) (sim_state : state)
        : config * eff =
    let msg_match_fail () : config * eff =
      (debugging_message
       (fun ppf ->
          fprintf ppf
          "@[message@ match@ failure@ at@ simulator:@ %n:@ %a@]"
          base pp_symb_pair sim_sp);
       fail_out_of_running_or_sending_config (ConfigIdealSending c)) in
    match c.sme with
    | SMET_Ord sme_ord ->
        let (root, _) = sim_sp in
        let sim_bt = unloc (IdPairMap.find sim_sp c.maps.sim_map) in
        let {id = state_id; args = state_args} = sim_state in
        let state_bt = unloc (IdMap.find state_id sim_bt.states) in
        (match sme_ord.path.inter_id_path with
         | [root'; basic'] ->
              if root' = root && basic' = sim_bt.uses && sme_ord.dir = Out
              then let source_addr =
                     match try_destr_port_as_func_rel source_port with
                     | None          -> failure "cannot happen"
                     | Some (rel, _) -> rel in
                   let () =
                     match sim_rf_addr with
                     | None      -> ()
                     | Some addr ->
                         assert (addr = source_addr) in
                   let sme_ord =
                     drop_head_of_msg_path_in_sent_msg_expr_ord_tyd sme_ord in
                   let (lc, ins) =
                     match_ord_sme_in_state true
                     (addr_concat_form_from_list_smart func_form source_addr)
                     state_bt state_args sme_ord in
                   (ConfigIdealRunning
                    {maps = c.maps;
                     gc   = c.gc;
                     pi   = c.pi;
                     dbs  = c.dbs;
                     iw   = c.iw;
                     ig   = c.ig;
                     iws  =
                       if i = -1
                       then {c.iws with
                             main_sim_state =
                               set_addr_if_none_in_sim_state
                               c.iws.main_sim_state source_addr}
                       else {c.iws with
                             other_sims_states =
                             List.modify_at i
                             (fun ss ->
                               set_addr_if_none_in_sim_state ss
                               source_addr)
                             c.iws.other_sims_states};
                     iwrc =
                       if i = -1
                       then IWRC_MainSim (base, sim_sp, state_id)
                       else IWRC_OtherSim (base, sim_sp, state_id, i);
                     path = sim_path;
                     lc   = lc;
                     ins  = create_instr_interp_list ins},
                    EffOK)
              else msg_match_fail ()
         | _               -> msg_match_fail ())
    | SMET_EnvAdv _    -> msg_match_fail () in

  let dest_ge_func_to_sim_cont_adv_party (i : int) (sim_sp : symb_pair)
      (sim_path : path)  (base : int) (sim_bt : sim_body_tyd)
      (sim_rf_addr : int list) (sim_state : state) : config * eff =
    let (root, _) = sim_sp in
    let msg_match_fail () : config * eff =
      (debugging_message
       (fun ppf ->
          fprintf ppf
          "@[message@ match@ failure@ at@ simulator:@ %n:@ %a@]"
          base pp_symb_pair sim_sp);
       fail_out_of_running_or_sending_config (ConfigIdealSending c)) in
    let check_path (sme_ord : sent_msg_expr_ord_tyd)
          : sent_msg_expr_ord_tyd option =
      let ft = IdPairMap.find (root, sim_bt.sims) c.maps.fun_map in
      match id_adv_inter_of_fun_tyd ft with
      | None          -> None
      | Some comp_adv ->
          match sme_ord.path.inter_id_path with
          | [root'; comp'; sub'] ->
              if root' = root && comp' = comp_adv && sme_ord.dir = In
              then match check_sub_interface_and_get_pi c.maps
                         root comp_adv sub' with
                   | None     -> failure "should not happen"
                   | Some ind ->
                       let src_adv_pi = base + ind in
                       if equal_port_index_of_port c.gc pi dbs
                          source_port src_adv_pi
                         then Some
                              (subst_for_iip_in_sent_msg_expr_ord_tyd
                               sme_ord [sim_bt.sims; comp_adv; sub'])
                         else None
              else None
          | _                    -> None in
    match c.sme with
    | SMET_Ord sme_ord ->
        let {id = state_id; args = state_args} = sim_state in
        let state_bt = unloc (IdMap.find state_id sim_bt.states) in
        (match check_path sme_ord with
         | None         -> msg_match_fail ()
         | Some sme_ord ->
             let (lc, ins) =
               match_ord_sme_in_state true
               (addr_concat_form_from_list_smart func_form sim_rf_addr)
               state_bt state_args sme_ord in
             (ConfigIdealRunning
              {maps = c.maps;
               gc   = c.gc;
               pi   = c.pi;
               dbs  = c.dbs;
               iw   = c.iw;
               ig   = c.ig;
               iws  = c.iws;
               iwrc =
                 if i = -1
                 then IWRC_MainSim (base, sim_sp, state_id)
                 else IWRC_OtherSim (base, sim_sp, state_id, i);
               path = sim_path;
               lc   = lc;
               ins  = create_instr_interp_list ins},
              EffOK))
    | SMET_EnvAdv _    -> msg_match_fail () in

  let dest_ge_func_to_sim_cont_param_or_sub_fun (i : int) (sim_sp : symb_pair)
      (sim_path : path) (base : int) (sim_bt : sim_body_tyd)
      (sim_rf_addr : int list) (sim_state : state) (expect_iip : string list)
      (new_iip : string list) (expect_source_adv_pi : int)
        : config * eff =
    let msg_match_fail () : config * eff =
      (debugging_message
       (fun ppf ->
          fprintf ppf
          "@[message@ match@ failure@ at@ simulator:@ %n:@ %a@]"
          base pp_symb_pair sim_sp);
       fail_out_of_running_or_sending_config (ConfigIdealSending c)) in
    match c.sme with
    | SMET_Ord sme_ord ->
        let {id = state_id; args = state_args} = sim_state in
        let state_bt = unloc (IdMap.find state_id sim_bt.states) in
        (match check_and_subst_for_iip_in_sent_msg_expr_ord_tyd sme_ord
               expect_iip new_iip with
         | None         -> msg_match_fail ()
         | Some sme_ord ->
             if sme_ord.dir = In &&
                equal_port_index_of_port c.gc pi dbs
                source_port expect_source_adv_pi
             then let (lc, ins) =
                    match_ord_sme_in_state true
                    (addr_concat_form_from_list_smart func_form sim_rf_addr)
                    state_bt state_args sme_ord in
                  (ConfigIdealRunning
                   {maps = c.maps;
                    gc   = c.gc;
                    pi   = c.pi;
                    dbs  = c.dbs;
                    iw   = c.iw;
                    ig   = c.ig;
                    iws  = c.iws;
                    iwrc =
                      if i = -1
                      then IWRC_MainSim (base, sim_sp, state_id)
                      else IWRC_OtherSim (base, sim_sp, state_id, i);
                    path = sim_path;
                    lc   = lc;
                    ins  = create_instr_interp_list ins},
                   EffOK)
             else msg_match_fail ())
    | SMET_EnvAdv _    -> msg_match_fail () in

  let dest_ge_func_to_sim (i : int) (sim_sp : symb_pair) (sim_path : path)
      (base : int) (rf_arg_adv_pis : int list) (sim_rf_addr : int list)
      (sim_st : state) : config * eff =
    let (root, _) = sim_sp in
    let sbt = unloc (IdPairMap.find sim_sp c.maps.sim_map) in
    let sim_rf = sbt.sims in
    let sim_ft = IdPairMap.find (root, sim_rf) c.maps.fun_map in
    let sim_rfbt = real_fun_body_tyd_of (unloc sim_ft) in
    let sim_rf_num_params = IdMap.cardinal sim_rfbt.params in
    let sim_rf_params_info : (symbol list * symbol list * int) list =
      List.mapi
      (fun i (param_id, (param_root, _, _)) ->
         let uior = unit_info_of_root c.maps param_root in
         let basic_adv_id = basic_adv_of_ideal_fun_of_triple_unit uior in
         ([param_root; basic_adv_id],
          [sim_rf; param_id; basic_adv_id],
          List.nth rf_arg_adv_pis i))
      (indexed_map_to_list_keep_keys sim_rfbt.params) in
    let sim_rf_num_adv_pis_of_parties =
      num_adv_pis_of_parties_of_real_fun c.maps root sim_ft in
    let sim_rf_num_sub_funs = IdMap.cardinal sim_rfbt.sub_funs in
    let sim_rf_sub_funs_info : (symbol list * symbol list * int) option list =
      List.mapi
      (fun i (sub_fun_id, (sf_root, sf_id, _)) ->
         match id_adv_inter_of_fun_tyd
               (IdPairMap.find (sf_root, sf_id) c.maps.fun_map) with
         | None              -> None
         | Some basic_adv_id ->
             Some
             ([sf_root; basic_adv_id],
              [sim_rf; sub_fun_id; basic_adv_id],
              base + sim_rf_num_adv_pis_of_parties + 1 + i))
      (IdMap.bindings sim_rfbt.sub_funs) in
    let find_param_or_sub_fun () :
          (symbol list * symbol list * int) option =
      let rec find_param (i : int) : int option =
        if i > sim_rf_num_params
        then None
        else let addr = sim_rf_addr @ [i] in
             if equal_func_rel_addr_of_port c.gc pi dbs
                dest_port addr
             then Some i
             else find_param (i + 1) in
      let rec find_sub_fun (i : int) : int option =
        if i > sim_rf_num_sub_funs
        then None
        else let addr = sim_rf_addr @ [sim_rf_num_params + i] in
             if equal_func_rel_addr_of_port c.gc pi dbs
                dest_port addr
             then Some i
             else find_sub_fun (i + 1) in
      match try_destr_port_as_func_rel dest_port with
      | None          ->
          (match find_param 1 with
           | None   ->
               (match find_sub_fun 1 with
                | None   -> None
                | Some i -> List.nth sim_rf_sub_funs_info (i - 1))
           | Some i -> Some (List.nth sim_rf_params_info (i - 1)))
      | Some (rel, _) ->
          (assert (List.length rel = List.length sim_rf_addr + 1);
           let i = List.last rel in
           if i < 1
             then None
           else if i <= sim_rf_num_params
             then Some (List.nth sim_rf_params_info (i - 1))
           else let i = i - sim_rf_num_params in
                if i > sim_rf_num_sub_funs
                then None
                else List.nth sim_rf_sub_funs_info (i - 1)) in
    let failure_msg () =
      (debugging_message
       (fun ppf ->
          fprintf ppf
          ("@[destination@ address@ of@ message@ does@ not@ correspond@ "  ^^
           "to@ argument@ or@ subfunctionality@ of@ real@ functionality@ " ^^
           "being@ simulated@ by:@ %n:@ %a@]")
          base pp_symb_pair sim_sp);
       fail_out_of_running_or_sending_config (ConfigIdealSending c)) in
    if equal_func_rel_addr_of_port c.gc pi dbs dest_port sim_rf_addr
    then dest_ge_func_to_sim_cont_adv_party i sim_sp sim_path base sbt
         sim_rf_addr sim_st
    else match find_param_or_sub_fun () with
         | None                                             -> failure_msg ()
         | Some (expect_iip, new_iip, expect_source_adv_pi) ->
             dest_ge_func_to_sim_cont_param_or_sub_fun i sim_sp sim_path
             base sbt sim_rf_addr sim_st expect_iip new_iip
             expect_source_adv_pi in

  (* i is the starting point: -1 <= i <= List.length
     c.iws.other_sims_states - 1

     should only be called for message whose destination address
     is >= func_form *)

  let from_adv_to_sim_or_ideal_func (i : int) : config * eff =
    match find_sim_from_right i with
    | None                                                       ->
        let (func_sp, base, path) = c.iw.iw_ideal_func in
        let fbt = unloc (IdPairMap.find func_sp c.maps.fun_map) in
        let ifbt = ideal_fun_body_tyd_of fbt in
        from_adv_or_sim_to_ideal_fun func_sp path base ifbt
    | Some (i, sim_sp, sim_path, adv_pi, rf_arg_adv_pis, sim_st) ->
        let {addr = sim_addr; state = sim_st} = sim_st in
        let sim_rf_addr = oget sim_addr in
        dest_ge_func_to_sim i sim_sp sim_path adv_pi rf_arg_adv_pis sim_rf_addr
        sim_st in

  (* i is the sending point:
     -1 <= i <= List.length c.iws.other_sims_states - 1

     depending upon whether the message goes left or right, the
     starting point is i - 1 or i + 1, repectively, unless that
     takes us to out of range - meaning the ideal functionality
     or the adversary *)

  let from_sim_left_or_right (i : int) : config * eff =
    if equal_adv_addr_of_port c.gc pi dbs dest_port
      then if i = List.length c.iws.other_sims_states - 1
           then msg_out_of_sending_config (ConfigIdealSending c) CtrlAdv
           else let dest_pi =
                  match try_destr_port_as_port_index dest_port with
                  | None       -> failure "cannot happen"
                  | Some porti -> porti in
                match find_sim_from_left (i + 1) dest_pi with
                | None                                          ->
                    msg_out_of_sending_config (ConfigIdealSending c) CtrlAdv
                | Some (i, sim_sp, sim_path, adv_pi, _, sim_st) ->
                    let {addr = sim_rf_addr; state = sim_st} = sim_st in
                    dest_adv_to_sim i sim_sp sim_path adv_pi sim_rf_addr sim_st
    else if greater_than_or_equal_func_rel_addr_of_port c.gc pi dbs
            dest_port []
      then if i = -1
           then let (func_sp, base, path) = c.iw.iw_ideal_func in
                let fbt = unloc (IdPairMap.find func_sp c.maps.fun_map) in
                let ifbt = ideal_fun_body_tyd_of fbt in
                from_adv_or_sim_to_ideal_fun func_sp path base ifbt
           else match find_sim_from_right (i - 1) with
                | None                                                       ->
                    let (func_sp, base, path) = c.iw.iw_ideal_func in
                    let fbt = unloc (IdPairMap.find func_sp c.maps.fun_map) in
                    let ifbt = ideal_fun_body_tyd_of fbt in
                    from_adv_or_sim_to_ideal_fun func_sp path base ifbt
                | Some (i, sim_sp, sim_path, adv_pi, rf_arg_adv_pis, sim_st) ->
                    let {addr = sim_addr; state = sim_st} = sim_st in
                    let sim_rf_addr = oget sim_addr in
                    dest_ge_func_to_sim i sim_sp sim_path adv_pi rf_arg_adv_pis
                    sim_rf_addr sim_st
    else failure "should not happen" in

  let from_adv () : config * eff =
    if mode = Dir ||
       greater_than_or_equal_adv_addr_of_port c.gc pi dbs dest_port ||
       not (equal_adv_addr_of_port c.gc pi dbs source_port) ||
       less_than_port_index_of_port c.gc pi dbs source_port 0
      then fail_out_of_running_or_sending_config (ConfigIdealSending c)
    else if greater_than_or_equal_func_rel_addr_of_port c.gc pi dbs dest_port []
      then if equal_port_index_of_port c.gc pi dbs source_port 0
           then fail_out_of_running_or_sending_config (ConfigIdealSending c)
           else from_adv_to_sim_or_ideal_func
                (List.length c.iws.other_sims_states - 1)
    else if equal_port_index_of_port c.gc pi dbs source_port 0 =
            equal_env_root_port c.gc pi dbs dest_port
      then msg_out_of_sending_config (ConfigIdealSending c) CtrlEnv
    else fail_out_of_running_or_sending_config (ConfigIdealSending c) in

  let from_ideal_func (fun_sp : symb_pair) : config * eff =
    match mode_of_sent_msg_expr_tyd c.sme with
    | Dir ->
       let sme = c.sme in
       let dest_port = dest_port_of_sent_msg_expr_tyd sme in
         if try eval_bool_form_to_bool c.gc pi dbs
                (envport_form func_form dest_port) with
            | ECProofEngine -> raise StepBlockedPortOrAddrCompare
         then msg_out_of_sending_config (ConfigIdealSending c) CtrlEnv
         else (debugging_message
               (fun ppf ->
                  fprintf ppf
                  "@[envport@ failure@ of@ destination@ port@ at@ %a@]"
                  pp_symb_pair fun_sp);
               fail_out_of_running_or_sending_config (ConfigIdealSending c))
    | Adv ->
        (let dest_pi =
           match try_destr_port_as_port_index dest_port with
           | None       -> failure "cannot happen"
           | Some porti -> porti in
         match find_sim_from_left (-1) dest_pi with
         | None                                ->
             msg_out_of_sending_config (ConfigIdealSending c) CtrlAdv
         | Some (i, sim_sp, sim_path, adv_pi, _, sim_st) ->
             let {addr = sim_rf_addr; state = sim_st} = sim_st in
             dest_adv_to_sim i sim_sp sim_path adv_pi sim_rf_addr sim_st) in

  try
    match c.iwsc with
    | IWSC_Env                    -> from_env ()
    | IWSC_Adv                    -> from_adv ()
    | IWSC_IdealFunc fun_sp       -> from_ideal_func fun_sp
    | IWSC_MainSim _              -> from_sim_left_or_right (-1)
    | IWSC_OtherSim (_, _, sim_i) -> from_sim_left_or_right sim_i

  with
  | ECProofEngine -> raise StepBlockedPortOrAddrCompare

let step_running_or_sending_real_or_ideal_config
    (conf : config)
    (ppi_opt : EcParsetree.pprover_infos option)
    (mod_dbs_opt : mod_dbs option)
      : config * eff =
  let pi =
    match ppi_opt with
    | None     -> prover_infos_of_config conf
    | Some ppi ->
        update_prover_infos (env_of_gc (gc_of_config conf))
        (prover_infos_of_config conf) ppi in
  let dbs =
    match mod_dbs_opt with
    | None         -> rewriting_dbs_of_config conf
    | Some mod_dbs ->
        modify_rewriting_dbs (env_of_gc (gc_of_config conf))
        (rewriting_dbs_of_config conf) mod_dbs in
  match conf with
  | ConfigRealRunning c  -> step_real_running_config c pi dbs
  | ConfigIdealRunning c -> step_ideal_running_config c pi dbs
  | ConfigRealSending c  -> step_real_sending_config c pi dbs
  | ConfigIdealSending c -> step_ideal_sending_config c pi dbs
  | _                    -> raise ConfigError
