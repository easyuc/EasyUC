(* UcSpec module *)

(* Specification Parse Trees

   This includes parse trees for specifications of functionalities,
   simulators and associated interfaces, but also for user input to
   the interpreter.

   We use EasyCrypt's parse trees for types (pty) and formulas
   (pformula).

   We still talk about "expressions" in the UC DSL, even though they
   are represented as formulas. They are the subset of formulas
   described by our grammar (see nonterminal `expr` of
   ucParser.mly). *)

open Format

open EcUtils
open EcLocation
open EcSymbols
open EcParsetree

open UcSpecTypedSpecCommon
open UcMessage

(* type bindings *)

type type_binding =
  {id : psymbol;  (* identifier *)
   ty : pty}      (* its type *)

(* messages *)

type message_body =
  {id     : psymbol;            (* name of message *)
   params : type_binding list}  (* typed parameters *)

type message_def =
  {dir    : msg_dir;            (* message direction *)
   id     : psymbol;            (* name of message *)
   params : type_binding list;  (* typed parameters *)
   port   : psymbol option}     (* optional port name -
                                   used in EasyCrypt code generation *)

(* interfaces: basic and composite; direct and adversarial *)

(* the components of composite interfaces are required to be basic
   ones *)

type comp_item =
  {sub_id   : psymbol;  (* name of sub-interface *)
   inter_id : psymbol}  (* name of basic interface - interpreted
                           in the same root (of .uc file) *)

type inter =
  | Basic     of message_def list  (* basic interface *)
  | Composite of comp_item list    (* composite interface *)

type named_inter =
  {id    : psymbol;  (* name of interface *)
   inter : inter}    (* contents of interface *)

type inter_def =
  | DirectInter      of named_inter  (* direct interface *)
  | AdversarialInter of named_inter  (* adversarial interface *)

(* state machines *)

(* message and state expressions *)

type msg_expr =
  {path      : msg_path;               (* message path *)
   args      : pformula list located;  (* message arguments *)
   port_expr : pformula option}        (* message destination - port expr *)

type state_expr =
  {id   : psymbol;                (* state to transition to *)
   args : pformula list located}  (* arguments of new state *)

(* instructions *)

type send_and_transition =
  {msg_expr   : msg_expr;    (* message to send *)
   state_expr : state_expr}  (* state to transition to *)

type instruction_u =
  | Assign of lhs * pformula                       (* ordinary assignment *)
  | Sample of lhs * pformula                       (* sampling assignment *)
  | ITE of pformula * instruction list located *   (* if-then-else *)
           instruction list located option
  | Match of pformula * match_clause list located  (* match instruction *)
  | SendAndTransition of send_and_transition       (* send and transition *)
  | Fail                                           (* failure *)

and instruction = instruction_u located

and match_clause = ppattern * instruction list located

let isUnconditionalFailure (ill : instruction list located) =
  match (unloc ill) with
  | [instr] ->
      (match (unloc instr) with
       | Fail -> true
       | _    -> false)
  | _       -> false

(* state machines *)

type msg_match_clause =                 (* message match clause *)
  {msg_pat : symbol msg_pat;            (* message pattern *)
   code    : instruction list located}  (* code of clause *)

type state_code =
  {vars      : type_binding list;      (* typed local variables *)
   mmclauses : msg_match_clause list}  (* message match clauses *)

type state =
  {id     : psymbol;                    (* name of state *)
   params : type_binding list located;  (* typed state parameters *)
   code   : state_code}                 (* code of state *)

type state_def =  (* state definition *)
  | InitialState of state
  | FollowingState of state

(* functionalities and simulators *)

type party_def =
  {id     : psymbol;         (* name of party *)
   serves : pqsymbol list;   (* interfaces served *)
   states : state_def list}  (* state machine *)

type sub_fun_decl =     (* subfunctionality definition *)
  {id      : psymbol;   (* name of subfunctionality *)
   fun_qid : pqsymbol}  (* qualified name of ideal functionality *)

type fun_body_real =                   (* real functionality body *)
  {sub_fun_decls : sub_fun_decl list;  (* sub-functionalities *)
   party_defs    : party_def list}     (* party defintions *)

type fun_body =                     (* functionality body *)
  | FunBodyReal  of fun_body_real   (* real functionality *)
  | FunBodyIdeal of state_def list  (* ideal funcitonality *)

let is_real_fun_body (fb : fun_body) : bool =
  match fb with
  | FunBodyReal _  -> true
  | FunBodyIdeal _ -> false

type fun_param =        (* functionality parameter *)
  {id      : psymbol;   (* name of parameter to functionality *)
   dir_qid : pqsymbol}  (* qualified name of composite direct interface *)

type fun_def =                 (* functionality definition *)
  {id       : psymbol;         (* name of functionality *)
   params   : fun_param list;  (* parameters to functionality *)
   dir_id   : psymbol;         (* name of composite direct interface,
                                  interpreted in same root *)
   adv_id   : psymbol option;  (* optional name of adversarial interface,
                                  interpreted in same root *)
   fun_body : fun_body}        (* functionality body *)

type sim_def =                             (* simulator definition *)
  {id            : psymbol;                (* name of simulator *)
   uses          : psymbol;                (* name of basic adversarial
                                              interface (from ideal
                                              functionality),
                                              interpreted in same root *)
   sims          : psymbol;                (* name of real functionality
                                              being simulated, interpreted
                                              in same root *)
   sims_arg_qids : pqsymbol list located;  (* qualified names of ideal
                                              functionality arguments to
                                              simulated real functionalities *)
   states        : state_def list }        (* state machine *)

(* top-level defintions *)

type def =
  | InterDef of inter_def  (* interface *)
  | FunDef   of fun_def    (* functionality *)
  | SimDef   of sim_def    (* simulator *)

(* spec parameters *)

type spec_param =
  | SP_AbstractTypeDecl of ptydecl located    (* abstract type decl *)
  | SP_AbstractOpDecl   of poperator located  (* abstract operator decl *)
  | SP_Axiom            of paxiom located     (* axiom specification *)

(* spec's EC and UC clones *)

type spec_clone =
  | SC_ECClone of theory_cloning located   (* EC clone *)
  | SC_UCClone of psymbol *                (* UC clone: the root and *)
                  theory_cloning located   (* EC clone of "_" ^ root *)

type preamble =
  {uc_requires : psymbol list;           (* require .uc files *)
   ec_requires : (psymbol * bool) list;  (* require and optionally import
                                            .ec files; true means import *)
   spec_params : spec_param list;        (* parameters to spec *)
   spec_clones : spec_clone list}        (* ec and uc clones of spec *)

(* pretty printing help for the UC DSL to EasyCrypt translator

   these functions will be partially applied - all but the final
   formatter argument - during typechecking, and only after the
   declaration or cloning in question was already checked by EasyCrypt
   (but the supplied environment will be the one in which the checking
   as done); consequently, they should never raise exceptions

   when using them with fprint, use %t (not %a) *)

type ppna = formatter -> unit  (* pp with no argument *)

let ppna_list_sep sep (ppnas : ppna list) : ppna =
  fun ppf ->
  let rec f (ppnas : ppna list) (ppf : formatter) =
    match ppnas with
    | []            -> ()
    | [ppna]        -> ppna ppf
    | ppna :: ppnas ->
        fprintf ppf "%t%(%)%t" ppna sep (f ppnas) in
  fprintf ppf "@[%t@]" (f ppnas)

let pp_abstract_type_decl (ptyd : ptydecl) : ppna =
  fun (ppf : formatter) ->
    let name = unloc ptyd.pty_name in
    let tyvars = List.map (unloc |- fst) ptyd.pty_tyvars in
    match List.length tyvars with
    | 0 -> fprintf ppf "@[type@ %s.@]" name
    | 1 -> fprintf ppf "@[type@ %s@ %s.@]" (List.hd tyvars) name
    | _ ->
        fprintf ppf "@[type@ (%a)@ %s.@]"
        (EcPrinting.pp_list ",@ " pp_symbol) tyvars name

let pp_abstract_op_decl (env : EcEnv.env) (po : poperator) : ppna =
  fun (ppf : formatter) ->
    let ue = EcUnify.UniEnv.create None in
    let ppe = EcPrinting.PPEnv.ofenv env in
    let tags = List.map unloc po.po_tags in
    let name = unloc (po.po_name) in
    let pty =
      match po.po_def with
      | PO_abstr pty -> pty
      | _            -> failure "cannot happen" in
    let ty = EcTyping.transty EcTyping.tp_tydecl env ue pty in
    let pp_tags ppf =
      fprintf ppf "@[[%a]@]" (EcPrinting.pp_list "@ " pp_symbol) in
    match List.length tags with
    | 0 ->
        fprintf ppf "@[op@ %a@ :@ %a.@]"
        (EcPrinting.pp_opname ppe) (EcPath.fromqsymbol (qsymb_of_symb name))
        (EcPrinting.pp_type ppe) ty
    | _ ->
        fprintf ppf "@[op@ %a@ %a@ :@ %a.@]"
        pp_tags tags
        (EcPrinting.pp_opname ppe) (EcPath.fromqsymbol (qsymb_of_symb name))
        (EcPrinting.pp_type ppe) ty

let pgtybinding_to_ptybinding ((osyms, pgty) : pgtybinding)
      : ptybinding =
  (osyms,
   match pgty with
   | PGTY_Type pty -> pty
   | _             -> failure "cannot happen")

type aptybinding = symbol option list * EcAst.ty

let aptybindings_type_map (f : EcAst.ty -> EcAst.ty)
    (aptybs : aptybinding list) : aptybinding list =
  List.map (fun (osyms, ty) -> (osyms, f ty)) aptybs

let abs_ptybindings (env : EcEnv.env) (ue : EcUnify.unienv)
    (ptybs : ptybindings) : aptybinding list =
  List.map
  (fun (osyms, pty) ->
     (List.map (omap unloc) (List.map unloc osyms),
      EcTyping.transty EcTyping.tp_relax env ue pty))
  ptybs

let pp_aptybinding (ppe : EcPrinting.PPEnv.t) (ppf : formatter)
    ((osyms, ty) : aptybinding) : unit =
  let pp_osym (ppf : formatter) (osym : symbol option) =
    match osym with
    | None   -> fprintf ppf "_"
    | Some s -> fprintf ppf "%s" s in
  fprintf ppf "@[(@[%a@ :@ %a@])@]"
  (EcPrinting.pp_list "@ " pp_osym) osyms
  (EcPrinting.pp_type ppe) ty  

let add_aptybinding_to_env (env : EcEnv.env) ((osyms, ty) : aptybinding)
      : EcEnv.env =
  let locs =
    List.filter_map
    (omap (fun sym -> (EcIdent.create sym, EcBaseLogic.LD_var (ty, None))))
    osyms in
  let x = EcEnv.LDecl.init env ~locals:(List.rev locs) [] in
  EcEnv.LDecl.toenv x

let add_aptybindings_to_env (env : EcEnv.env) (aptybs : aptybinding list)
      : EcEnv.env =
  List.fold_left add_aptybinding_to_env env aptybs

let pp_aptybindings (ppe : EcPrinting.PPEnv.t) (ppf : formatter)
    (aptybs : aptybinding list) : unit =
  fprintf ppf "@[%a@]"
  (EcPrinting.pp_list "@ " (pp_aptybinding ppe)) aptybs

let pp_axiom (env : EcEnv.env) (pa : paxiom) : ppna =
  fun (ppf : formatter) ->
    let ue = EcUnify.UniEnv.create None in
    let name = unloc (pa.pa_name) in
    let ptybs_opt = omap (List.map pgtybinding_to_ptybinding) pa.pa_vars in
    let aptybs_opt = omap (abs_ptybindings env ue) ptybs_opt in
    let pf = pa.pa_formula in
    match aptybs_opt with
    | None        ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        let f = EcTyping.trans_form_opt env ue pf (Some EcTypes.tbool) in
        let uidmap =
          try EcUnify.UniEnv.close ue with
          | EcUnify.UninstanciateUni -> failure "cannot happen" in
        let ts = EcFol.Tuni.subst uidmap in
        let f = EcFol.Fsubst.f_subst ts f in
        fprintf ppf "@[axiom@ %s@ :@ %a.@]" name 
        (EcPrinting.pp_form ppe) f
    | Some aptybs ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        let env' = add_aptybindings_to_env env aptybs in
        let ppe' = EcPrinting.PPEnv.ofenv env' in
        let f = EcTyping.trans_form_opt env' ue pf (Some EcTypes.tbool) in
        let uidmap =
          try EcUnify.UniEnv.close ue with
          | EcUnify.UninstanciateUni -> failure "cannot happen" in
        let ts = EcFol.Tuni.subst uidmap in
        let subst_ty = EcFol.ty_subst ts in
        let aptybs = aptybindings_type_map subst_ty aptybs in
        let f = EcFol.Fsubst.f_subst ts f in
        fprintf ppf "@[axiom@ %s@ %a@ :@ %a.@]" name 
        (pp_aptybindings ppe) aptybs
        (EcPrinting.pp_form ppe') f

let pp_clmode (ppf : formatter) (clm : clmode) : unit =
  match clm with
  | `Alias         -> fprintf ppf "="
  | `Inline `Keep  -> fprintf ppf "<="
  | `Inline `Clear -> fprintf ppf "<-"

let pp_import (ppf : formatter) x : unit =
  match x with
  | `Include -> fprintf ppf "include"
  | `Import  -> fprintf ppf "import"
  | `Export  -> failure "cannot happen"

let qsym_to_sym ((syms, sym) : qsymbol) : symbol =
  if List.is_empty syms then sym else failure "cannot happen"

let by_syntax (x : 'a genoverride * clmode) : 'a * clmode =
  (match fst x with
   | `ByPath _   -> failure "cannot happen"
   | `BySyntax y -> y,
   snd x)

let pp_override (env : EcEnv.env) (ppf : formatter)
    ((pqsym, tho) : pqsymbol * theory_override) : unit =
  let name = unloc pqsym in
  match tho with
  | PTHO_Type tyo ->
      let name = qsym_to_sym name in
      let ue = EcUnify.UniEnv.create None in
      let ppe = EcPrinting.PPEnv.ofenv env in
      let ((psyms, pty), clm) = by_syntax tyo in
      let tyvars = List.map unloc psyms in
      let ty = EcTyping.transty EcTyping.tp_tydecl env ue pty in
       (match List.length tyvars with
        | 0 ->
            fprintf ppf "@[type@ %s@ %a@ %a@]" name pp_clmode clm
            (EcPrinting.pp_type ppe) ty  
        | 1 ->
            fprintf ppf "@[type@ %s@ %s@ %a@ %a@]" (List.hd tyvars)
            name pp_clmode clm (EcPrinting.pp_type ppe) ty  
        | _ ->
            fprintf ppf "@[type@ (%a)@ %s@ %a@ %a@]"
            (EcPrinting.pp_list ",@ " pp_symbol) tyvars
            name pp_clmode clm (EcPrinting.pp_type ppe) ty)
  | PTHO_Op opo   ->
      let (opod, clm) = by_syntax opo in
      let () = if opod.opov_tyvars <> None then failure "cannot happen" in
      let args = opod.opov_args in
      let pty = opod.opov_retty in
      let pf = opod.opov_body in
      let ue = EcUnify.UniEnv.create None in
      let ty = EcTyping.transty EcTyping.tp_relax env ue pty in
      let args = abs_ptybindings env ue args in
      let env' = add_aptybindings_to_env env args in
      let ppe = EcPrinting.PPEnv.ofenv env' in
      let f = EcTyping.trans_form_opt env' ue pf (Some ty) in
      let uidmap =
        try EcUnify.UniEnv.close ue with
        | EcUnify.UninstanciateUni -> failure "cannot happen" in
      let ts = EcFol.Tuni.subst uidmap in
      let subst_ty = EcFol.ty_subst ts in
      let subst_form = EcFol.Fsubst.f_subst ts in
      let args = aptybindings_type_map subst_ty args in
      let ty = subst_ty ty in
      let f = subst_form f in
      (match List.length args with
       | 0 ->
           fprintf ppf "@[op@ %a@ :@ %a@ %a@ %a@]"
           (EcPrinting.pp_opname ppe) (EcPath.fromqsymbol name)
           (EcPrinting.pp_type ppe) ty pp_clmode clm
           (EcPrinting.pp_form ppe) f
       | _ ->
           fprintf ppf "@[op@ %a@ %a@ :@ %a %a@ %a@]"
           (EcPrinting.pp_opname ppe) (EcPath.fromqsymbol name)
           (pp_aptybindings ppe) args (EcPrinting.pp_type ppe) ty
           pp_clmode clm (EcPrinting.pp_form ppe) f)
  | _             -> failure "cannot happen"

type clone_type =
  | ECCloneType
  | UCCloneType

let pp_clone_type (ppf : formatter) (ct : clone_type) : unit =
  match ct with
  | ECCloneType -> fprintf ppf "ec_clone"
  | UCCloneType -> fprintf ppf "uc_clone"

let pp_theory_cloning (ct : clone_type) (env : EcEnv.env) (tc : theory_cloning)
      : ppna =
  fun (ppf : formatter) ->
    let () =
      if tc.pthc_prf <> [] || tc.pthc_rnm <> [] || tc.pthc_clears <> [] ||
         tc.pthc_opts <> [] || tc.pthc_local <> None
      then failure "cannot happen" in
    let import_opt = tc.pthc_import in
    let base = unloc tc.pthc_base in
    let name_opt = omap unloc tc.pthc_name in
    let overs = tc.pthc_ext in
    let ppna_first ppf =
      match import_opt with
      | None        -> fprintf ppf "%a@ %a" pp_clone_type ct pp_qsymbol base
      | Some import ->
        fprintf ppf "%a@ %a@ %a"
        pp_clone_type ct pp_import import pp_qsymbol base in
    let ppna_second ppf =
      match name_opt with
      | None      -> fprintf ppf "%t" ppna_first
      | Some name -> fprintf ppf "%t@ as@ %s" ppna_first name in
    match List.length overs with
    | 0 -> fprintf ppf "@[%t.@]" ppna_second
    | _ ->
        fprintf ppf "@[%t@ with@\n@ @ @[%a@].@]"
        ppna_second (EcPrinting.pp_list ",@\n" (pp_override env)) overs

(*
  | x = loc(EC_CLONE); ip = clone_import?; base = uqident;
    name = prefix(AS, uident)?; cw = clone_with?
      { mk_loc (loc x)
        { pthc_base   = base;
          pthc_name   = name;
          pthc_ext    = EcUtils.odfl [] cw;
          pthc_prf    = [];
          pthc_rnm    = [];
          pthc_clears = [];
          pthc_opts   = [];
          pthc_local  = None;
          pthc_import = ip; }
      }

psymbol = symbol located
pqsymbol = qsymbol located
pp_symbol
pp_qsymbol

type ptybinding  = osymbol list * pty
and  ptybindings = ptybinding list

type osymbol_r   = psymbol option
type osymbol     = osymbol_r located

type theory_cloning = {
  pthc_base   : pqsymbol;
  pthc_name   : psymbol option
  pthc_ext    : (pqsymbol * theory_override) list;
  pthc_prf    : []
  pthc_rnm    : []
  pthc_opts   : []
  pthc_clears : []
  pthc_local  : None
  pthc_import : [`Import | `Include] option;
}

and theory_override =
| PTHO_Type   of ty_override
| PTHO_Op     of op_override

and ty_override = ty_override_def genoverride * clmode
and op_override = op_override_def genoverride * clmode

and clmode = [`Alias | `Inline of [`Keep | `Clear]]

and 'a genoverride = [
| `ByPath   of not used
| `BySyntax of 'a
]

and ty_override_def = psymbol list * pty

and op_override_def = {
  opov_tyvars : psymbol list option; (should be None)
  opov_args   : ptybinding list;
  opov_retty  : pty;
  opov_body   : pformula;
}

*)

(* overall UC specifications *)

type spec =
  {preamble    : preamble;
   definitions : def list}

(* functionality expression

   when a functionality has "()" as its argument list, we use
   FunExprArgs (with []), but if it has no argument list, we use
   FunExprNoArgs

   in typechecking, we will forbid ideal functionalities with an
   empty argument list, insisting on form FunExprNoArgs *)

type fun_expr =
  | FunExprNoArgs of pqsymbol
  | FunExprArgs   of pqsymbol * fun_expr list

let loc_of_fun_expr (fe : fun_expr) : EcLocation.t =
  match fe with
  | FunExprNoArgs pqsym    -> loc pqsym
  | FunExprArgs (pqsym, _) -> loc pqsym

(* for use in sent message expr *)

type port_or_addr =
  | PoA_Port of pformula
  | PoA_Addr of pformula

let loc_of_port_or_addr (poa : port_or_addr) : EcLocation.t =
  match poa with
  | PoA_Port pformula -> loc pformula
  | PoA_Addr pformula -> loc pformula

(* expression for message in transit (sent message expession)

   there are two forms, ordinary and for environment/adversary
   communication

   -- ordinary --

   message path must be qualified by root, as otherwise could
   be ambiguous

   source or destination can be an address, when the port index
   is implicit from the message path

   when it's the *source* whose port index is being inferred, this
   will be possible iff the message direction is "out" and either the
   message path terminates in a component of a composite interface or
   terminates with the basic adversarial interface of an ideal
   functionality

   when it's the *destination* whose port index is being inferred,
   this will be possible iff the message direction is "in" and either the
   message path terminates in a component of a composite interface or
   terminates with the basic adversarial interface of an ideal
   functionality

   -- environment/adversary communication --

   this form carries no data, and has both source and destination ports.
   its function is to model whatever communication the environment
   and adversary are carrying out (which would pass data) *)

type sent_msg_expr_ord =
  {src_poa  : port_or_addr;           (* source *)
   path     : msg_path;               (* message path *)
   args     : pformula list located;  (* message arguments *)
   dest_poa : port_or_addr}           (* destination *)

type sent_msg_expr_env_adv =
  {src_port  : pformula;   (* source *)
   dest_port : pformula }  (* destination *)

type sent_msg_expr =
  | SME_Ord    of sent_msg_expr_ord
  | SME_EnvAdv of sent_msg_expr_env_adv

let loc_of_src_of_sent_msg_expr (sme : sent_msg_expr) : EcLocation.t =
  match sme with
  | SME_Ord sme    -> loc_of_port_or_addr sme.src_poa
  | SME_EnvAdv sme -> loc sme.src_port

let loc_of_dest_of_sent_msg_expr (sme : sent_msg_expr) : EcLocation.t =
  match sme with
  | SME_Ord sme    -> loc_of_port_or_addr sme.dest_poa
  | SME_EnvAdv sme -> loc sme.dest_port

(* rewriting databases modification *)

(* the first component is what should be removed; the second
   component is what should then be added *)

type mod_dbs = pqsymbol list * pqsymbol list

(* Interpreter User Input *)

type world =
  | Real
  | Ideal

type control =
  | CtrlEnv
  | CtrlAdv

type peff_r =
  | EffOK
  | EffRand
  | EffMsgOut of sent_msg_expr * control
  | EffFailOut

type peff = peff_r located

type interpreter_command_u =
  | Load   of psymbol
  | FunEx  of fun_expr
  | World  of world
  | Send   of sent_msg_expr
  | Run    of int option
  | Step   of EcParsetree.pprover_infos option * mod_dbs option
  | AddVar of type_binding
  | AddAss of psymbol * pformula
  | Prover of EcParsetree.pprover_infos
  | Hint   of mod_dbs
  | Finish
  | Assert of peff
  | Debug
  | Undo   of int located
  | Quit

type interpreter_command = interpreter_command_u located
