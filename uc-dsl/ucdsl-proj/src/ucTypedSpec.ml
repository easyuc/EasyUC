(* UcTypedSpec module *)

(* Typed Specifications

   This includes specifications of functionalities, simulators and
   associated interfaces, but also for user input to the
   interpreter.

   We use the EasyCrypt types `ty` (types) and `form` (formulas).
   Only a subset of formulas can be expressed in our grammar
   (see `expr` of ucParser.mly); we consider these "expressions". *)

open Format

open EcLocation
open EcUtils
open EcSymbols
open EcTypes
open EcFol

open UcSpecTypedSpecCommon
open UcPreamblePP
open UcMessage

(* the term "id" or "identifier" is used in our code for several
   related things:

   * sometimes it's a symbol (i.e., a string);

   * sometimes it's a located symbol, in which case we may use "uid" to
     stand for the unlocated version;

   * sometimes it's a value of type EcIdent.t *)

(* maps and sets *)

(* maps and sets of values of type EcIdent.t *)

module Mid = EcIdent.Mid
module Sid = EcIdent.Sid

module IdMap = Map.Make(String)  (* domain: string = symbol *)
module IdSet = Set.Make(String)

let exists_id (id_map : 'a IdMap.t) (id : symbol) : bool =
  IdMap.exists (fun key _ -> key = id) id_map

let id_map_domain (map : 'a IdMap.t) : IdSet.t =
  IdSet.of_list (List.map fst (IdMap.bindings map))

(* map back and forth between the keys of an IdMap and their
   ordinal numbers, beginning from 0, i.e., their positions
   in the list of keys sorted in lexicographic order *)

let id_map_ordinal_of_sym (map : 'a IdMap.t) (id : symbol) : int =
  let bndgs = IdMap.bindings map in
  fst (List.findi (fun _ (x, _) -> x = id) bndgs)

let id_map_sym_of_ordinal (map : 'a IdMap.t) (i : int) : symbol =
  let bndgs = IdMap.bindings map in
  fst (List.nth bndgs i)

(* map back and forth between the keys of an IdMap and their
   ordinal numbers, beginning from 1, i.e., their positions
   in the list of keys sorted in lexicographic order *)

let id_map_ordinal1_of_sym (map : 'a IdMap.t) (id : symbol) : int =
  id_map_ordinal_of_sym map id + 1

let id_map_sym_of_ordinal1 (map : 'a IdMap.t) (i : int) : symbol =
  let bndgs = IdMap.bindings map in
  fst (List.nth bndgs (i - 1))

module SL =  (* domain: string list = symbol list *)
  struct
    type t = string list
    (* lexicographic ordering, using lexicographic ordering on
       individual strings *)
    let compare = List.compare String.compare
  end

let sing_elt_of_id_set (id_set : IdSet.t) : symbol =
  match IdSet.elements id_set with
  | [x] -> x
  | _   -> failure "cannot happen"

(* we often refer to elements of type symbol list as "qualified ids";
   note that qsymbol stands for symbol list * symbol *)

module QidMap = Map.Make(SL)
module QidSet = Set.Make(SL)

let exists_qid (qid_map : 'a QidMap.t) (qid : symbol list) : bool =
  QidMap.exists (fun key _ -> key = qid) qid_map

let qid_map_domain (map : 'a QidMap.t) : QidSet.t =
  QidSet.of_list (List.map fst (QidMap.bindings map))

type symb_pair = symbol * symbol

module SP =  (* domain: string * string = symb_pair *)
  struct
    type t = string * string
    (* lexicogrphic ordering, using lexicographic ordering on strings *)
    let compare = Stdlib.compare
  end

module IdPairMap = Map.Make(SP)
module IdPairSet = Set.Make(SP)

(* we often refer to elements of symb_pair as id pairs

   for an id pair (x, y), x is the capitalized root name of a .uc
   file, and y is the capitalized name of an interface, functionality
   or simulator from that file *)

let exists_id_pair
    (id_pair_map : 'a IdPairMap.t) (id_pair : symb_pair) : bool =
  IdPairMap.exists (fun key _ -> key = id_pair) id_pair_map

let id_pair_map_domain (map : 'a IdPairMap.t) : IdPairSet.t =
  IdPairSet.of_list (List.map fst (IdPairMap.bindings map))

let pp_qsymbol_abbrev
    (root : symbol) (ppf : Format.formatter) ((xs, y) : qsymbol) : unit =
  if xs = [root]
  then pp_symbol ppf y
  else pp_qsymbol ppf (xs, y)

let id_pair_to_qsymbol ((x, y) : symb_pair) : qsymbol = ([x], y)

let pp_id_pair (ppf : Format.formatter) (id_pair : symb_pair) =
  pp_qsymbol ppf (id_pair_to_qsymbol id_pair)

let pp_id_pair_abbrev
    (root : symbol) (ppf : Format.formatter) (id_pair : symb_pair) : unit =
  pp_qsymbol_abbrev root ppf (id_pair_to_qsymbol id_pair)

let nonempty_qid_to_qsymbol (xs : SL.t) : qsymbol =
  let len = List.length xs in
  (Batteries.List.take (len - 1) xs, Batteries.List.last xs)

let nonempty_qid_to_string (xs : SL.t) : string =
  List.fold_left (fun s x -> if s <> "" then s ^ "." ^ x else x) "" xs

let get_keys_as_sing_qids (m : 'a IdMap.t) : QidSet.t =
  let ids = fst (List.split (IdMap.bindings m)) in
  QidSet.of_list (List.map (fun id -> [id]) ids)

let indexed_map_to_list (mapind : ('o * int) IdMap.t) : 'o list =
  let l = IdMap.fold (fun _ v l -> v :: l) mapind [] in
  let lord = List.sort (fun a1 a2 -> snd a1 - snd a2) l in
  List.map (fun a -> fst a) lord

let indexed_map_to_list_keep_keys (mapind : ('o * int) IdMap.t) :
  (symbol * 'o) list =
  List.map
  (fun (s, (x, _)) -> (s, x))
  (List.sort
   (fun (_, (_, a1)) (_, (_, a2)) -> a1 - a2)
   (IdMap.bindings mapind))

let indexed_map_to_list_only_keep_keys (mapind : ('o * int) IdMap.t) :
  symbol list =
  List.map
  (fun (s, _) -> s)
  (List.sort
   (fun (_, (_, a1)) (_, (_, a2)) -> a1 - a2)
   (IdMap.bindings mapind))

let filter_map (fm : 'a -> 'b option) (m : 'a IdMap.t) : 'b IdMap.t =
  let flt =
    IdMap.filter
    (fun _ def ->
       match fm def with
       | Some _ -> true
       | None   -> false)
    m in
  IdMap.map
  (fun def ->
     match fm def with
     | Some x -> x
     | None -> raise (Failure "!impossible!"))
  flt

let unlocm (lm : 'a located IdMap.t) : 'a IdMap.t =
  IdMap.map (fun al -> unloc al) lm

let unloc_ident_map (lm : 'a located Mid.t) : 'a Mid.t =
  Mid.map (fun al -> unloc al) lm

(* located type plus an index, starting from 0 *)

type ty_index = (ty * int) located

(* UC DSL and EasyCrypt types *)

let uc_qsym_prefix_basic_types = ["Top"; "UCBasicTypes"]
let uc_qsym_prefix_list_po     = ["Top"; "UCListPO"]
let ec_qsym_prefix_core_int    = ["Top"; "CoreInt"]
let ec_qsym_prefix_list        = ["Top"; "List"]

let port_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "port")) []

let addr_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "addr")) []

(* UC DSL and EasyCrypt operators *)

let env_root_addr_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "env_root_addr")) []
  addr_ty

let env_root_port_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "env_root_port")) []
  port_ty

let adv_addr_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "adv")) []
  addr_ty

let adv_root_port_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "adv_root_port")) []
  port_ty

let envport_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "envport")) []
  (tfun addr_ty (tfun port_ty tbool))

let inc_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_list_po, "inc")) [tint]
  (tfun addr_ty (tfun addr_ty tbool))

let addr_le_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_list_po, "<=")) [tint]
  (tfun addr_ty (tfun addr_ty tbool))

let addr_lt_op : form =
  f_op (EcPath.fromqsymbol (uc_qsym_prefix_list_po, "<")) [tint]
  (tfun addr_ty (tfun addr_ty tbool))

let addr_concat_op : form =
  f_op (EcPath.fromqsymbol (ec_qsym_prefix_list, "++")) [tint]
  (tfun addr_ty (tfun addr_ty addr_ty))

let addr_nil_op : form =
  f_op
  (EcPath.fromqsymbol (ec_qsym_prefix_list, EcCoreLib.s_nil)) [tint] addr_ty

let addr_cons_op : form =
  f_op (EcPath.fromqsymbol (ec_qsym_prefix_list, EcCoreLib.s_cons)) [tint]
  (tfun tint (tfun addr_ty addr_ty))

let int_add_op : form =
  f_op (EcPath.fromqsymbol (ec_qsym_prefix_core_int, "add")) []
  (tfun tint (tfun tint tbool))

let int_lt_op : form =
  f_op (EcPath.fromqsymbol (ec_qsym_prefix_core_int, "lt")) []
  (tfun tint (tfun tint tbool))

let int_le_op : form =
  f_op (EcPath.fromqsymbol (ec_qsym_prefix_core_int, "le")) []
  (tfun tint (tfun tint tbool))

(* values of type EcIdent.t *)

let envport_id : EcIdent.t = EcIdent.create "envport"

(* substitution of path prefixes in types and formulas

   when using the following functions, none of the paths involved
   should, when converted to a symbol list, be equal to olds *)

let error_non_EasyUC_type_or_formula () =
  non_loc_error_message
  (fun ppf -> fprintf ppf "@[non-EasyUC@ type@ or@ formula@]")

let cond_subst_path_prefix (olds : SL.t) (news : SL.t) (p : EcPath.path)
      : EcPath.path =
  let ne_sym_list_to_path (symbs : symbol list) : EcPath.path =
    EcPath.fromqsymbol (nonempty_qid_to_qsymbol symbs) in
  let origs = EcPath.tolist p in
  let rec rem olds origs =
    match (olds, origs) with
    | (_,           [])            -> error_non_EasyUC_type_or_formula ()
    | ([],          _)             -> ne_sym_list_to_path (news @ origs)
    | (old :: olds, orig :: origs) ->
        if old = orig then rem olds origs else p in
  rem olds origs

let cond_subst_path_prefix_in_type (olds : SL.t) (news : SL.t) (ty : ty)
      : ty =
  let rec cond_subst_ty (ty : ty) =
    EcAst.mk_ty (cond_subst_ty_node ty.ty_node)
  and cond_subst_ty_node (node : ty_node) =
    match node with
    | Tglob   _        -> error_non_EasyUC_type_or_formula ()
    | Tunivar _        -> error_non_EasyUC_type_or_formula ()
    | Tvar x           -> Tvar x   
    | Ttuple tys       -> Ttuple (List.map cond_subst_ty tys)
    | Tconstr (p, tys) ->
        Tconstr
        (cond_subst_path_prefix olds news p,
         List.map cond_subst_ty tys)
    | Tfun (ty1, ty2)  -> Tfun (cond_subst_ty ty1, cond_subst_ty ty2) in
  cond_subst_ty ty

let cond_subst_path_prefix_in_form (olds : SL.t) (news : SL.t) (f : form)
      : form =
  let rec cond_subst_form (f : form) =
    EcAst.mk_form (cond_subst_f_node f.f_node)
    (cond_subst_path_prefix_in_type olds news f.f_ty)
  and cond_subst_f_node (node : f_node) =
    match node with
    | Fquant (q, bnds, f) ->
        let cond_subst_gty (gty : gty) =
          match gty with
          | GTty ty -> EcAst.GTty (cond_subst_path_prefix_in_type olds news ty)
          | _       -> error_non_EasyUC_type_or_formula () in
        Fquant
        (q,
         List.map
         (fun (id, gty) -> (id, cond_subst_gty gty))
         bnds,
         cond_subst_form f)
    | Fif (f1, f2, f3)    ->
        Fif (cond_subst_form f1, cond_subst_form f2, cond_subst_form f3)
    | Fmatch (f, fs, ty)  ->
        Fmatch
        (cond_subst_form f, List.map cond_subst_form fs,
         cond_subst_path_prefix_in_type olds news ty)
    | Flet (lpat, f1, f2) ->
        Flet (cond_subst_lpattern lpat, cond_subst_form f1, cond_subst_form f2)
    | Fint fzi            -> Fint fzi
    | Flocal id           -> Flocal id
    | Fop (p, tys)        ->
        Fop
        (cond_subst_path_prefix olds news p,
         List.map (cond_subst_path_prefix_in_type olds news) tys)
    | Fapp (f, fs)        ->
        Fapp (cond_subst_form f, List.map cond_subst_form fs)
    | Ftuple fs           -> Ftuple (List.map cond_subst_form fs)
    | Fproj (f, i)        -> Fproj (cond_subst_form f, i)
    | _                   -> error_non_EasyUC_type_or_formula ()
   and cond_subst_lpattern (lpat : lpattern) =
     match lpat with
     | LSymbol (id, ty)    ->
         LSymbol (id, cond_subst_path_prefix_in_type olds news ty)
     | LTuple  sbnds       ->
         LTuple
         (List.map
          (fun (id, ty) -> (id, cond_subst_path_prefix_in_type olds news ty))
          sbnds)
     | LRecord (p, osbnds) ->
         LRecord
         (cond_subst_path_prefix olds news p,
          List.map
          (fun (osbnd, ty) ->
             (osbnd, cond_subst_path_prefix_in_type olds news ty))
          osbnds) in
   cond_subst_form f

(* typed messages and functionality interfaces *)

type message_body_tyd =
  {dir        : msg_dir;           (* direction of message *)
   params_map : ty_index IdMap.t;  (* message parameters: index is
                                      parameter number *)
   port       : symbol option}     (* optional port name - used in generating
                                      EasyCrypt code *)

type basic_inter_body_tyd = message_body_tyd IdMap.t

(* inversion of direction *)

let invert_msg_dir (mdbt : message_body_tyd) : message_body_tyd =
  {mdbt with
     dir = invert_dir mdbt.dir}

let invert_basic_inter_body_tyd
    (bibt : basic_inter_body_tyd) : basic_inter_body_tyd =
  IdMap.map invert_msg_dir bibt

type inter_body_tyd =
  | BasicTyd     of basic_inter_body_tyd  (* basic interface *)
  | CompositeTyd of symbol IdMap.t        (* composite interface; symbol is
                                             name of basic interface -
                                             with same root *)

let is_basic_tyd (ibt : inter_body_tyd) : bool =
  match ibt with
  | BasicTyd _     -> true
  | CompositeTyd _ -> false

let is_composite_tyd (ibt : inter_body_tyd) : bool =
  match ibt with
  | BasicTyd _     -> false
  | CompositeTyd _ -> true

let basic_tyd_of_inter_body_tyd (ibt : inter_body_tyd) : basic_inter_body_tyd =
  match ibt with
  | BasicTyd bibt  -> bibt
  | CompositeTyd _ -> failure "should not happen"

let composite_map_of_inter_body_tyd (ibt : inter_body_tyd)
      : symbol IdMap.t =
  match ibt with
  | BasicTyd _      -> failure "should not happen"
  | CompositeTyd mp -> mp

type inter_tyd = inter_body_tyd located  (* typed interface *)

(* state machines, typed functionalities and simulators *)

(* message and state expressions *)

type msg_expr_tyd =
  {path      : msg_path;           (* message path *)
   args      : form list located;  (* message arguments *)
   port_expr : form option}        (* message destination - port expr *)

type state_expr_tyd =
  {id   : psymbol;            (* state to transition to *)
   args : form list located}  (* arguments of new state *)

(* instructions *)

type send_and_transition_tyd =
  {msg_expr   : msg_expr_tyd;    (* message to send *)
   state_expr : state_expr_tyd}  (* state to transition to *)

type bindings = (EcIdent.t located * ty) list

let unloc_bindings (bndgs : bindings) : (EcIdent.t * ty) list =
  List.map (fun (id, ty) -> (unloc id, ty)) bndgs

type instruction_tyd_u =
  | Assign of lhs * form                           (* ordinary assignment *)
  | Sample of lhs * form                           (* sampling assignment *)
  | ITE of form * instruction_tyd list located *   (* if-then-else *)
           instruction_tyd list located option
  | Match of form * match_clause_tyd list located  (* match instruction *)
  | SendAndTransition of send_and_transition_tyd   (* send and transition *)
  | Fail                                           (* failure *)

and instruction_tyd = instruction_tyd_u located

and match_clause_tyd = symbol * (bindings * instruction_tyd list located)

type msg_match_clause_tyd =                 (* message match clause *)
  {msg_pat : (EcIdent.t * ty) msg_pat;      (* message pattern *)
   code    : instruction_tyd list located}  (* code of clause *)

let msg_match_clause_msg_pat_bindings (mmc : msg_match_clause_tyd)
      : (EcIdent.t * ty) list =
  let msg_pat = mmc.msg_pat in
  (match msg_pat.port_id with
   | None   -> []
   | Some x -> [unloc x]) @
  (match msg_pat.pat_args with
   | None    -> []
   | Some xs ->
       let ys =
         List.map
           (fun pat ->
            match pat_id_data pat with
            | None   -> []
            | Some z -> [z])
         xs in
       List.concat ys)

type state_body_tyd =
  {is_initial     : bool;                       (* the initial state? *)
   params         : ty_index Mid.t;             (* typed parameters, index is
                                                   parameter number *)
   vars           : (EcIdent.t * ty) located    (* map from variables to *)
                    IdMap.t;                    (* identifiers and types *)
   internal_ports : EcIdent.t QidMap.t;         (* map from internal ports
                                                   to their identifiers *)
   mmclauses      : msg_match_clause_tyd list}  (* message match clauses *)

let vars_map_to_domain (mp : (EcIdent.t * ty) located IdMap.t) : IdSet.t =
  IdSet.of_list (List.map fst (IdMap.bindings mp))

type state_tyd = state_body_tyd located  (* typed state *)

(* return the set of possible next states of a located list of
   instructions that has already passed the control transfer
   checks (UcTypecheck.check_instrs_transfer_at_end) *)

let rec state_transitions_of_instrs (is : instruction_tyd list located)
          : IdSet.t =
  let uis = unloc is in
  match uis with
  | [] -> failure "should not happen"
  | is -> state_transitions_of_instr (List.last is)

and state_transitions_of_instr (instr : instruction_tyd) : IdSet.t =
  let uinstr = unloc instr in
  match uinstr with
  | Assign _                    -> failure "should not happen"
  | Sample _                    -> failure "should not happen"
  | ITE (_, thens, elses)       ->
      IdSet.union (state_transitions_of_instrs thens)
      (match elses with
       | None       -> failure "should not happen"
       | Some elses -> state_transitions_of_instrs elses)
  | Match (_, clauses)          ->
      List.fold_left
      (fun ids (_, (_, is)) ->
         IdSet.union ids (state_transitions_of_instrs is))
      IdSet.empty
      (unloc clauses)
  | SendAndTransition sat       ->
      IdSet.singleton (unloc sat.state_expr.id)
  | Fail                        -> IdSet.empty

(* return the set of possible next states of a typed state that has
   already passed the control transfer checks
   (UcTypecheck.check_instrs_transfer_at_end) *)

let state_transitions_of_state (st : state_tyd) : IdSet.t =
  let sbt = unloc st in
  List.fold_left
  (fun ids mmclause ->
     IdSet.union ids (state_transitions_of_instrs mmclause.code))
  IdSet.empty
  sbt.mmclauses

(* should only be called when the number of parameters and arguments
   are the same *)

let match_state_args (params : ty_index Mid.t) (args : 'a list)
      : (EcIdent.t * 'a) list =
  let bindings = Mid.bindings params in
  let idents =
    List.map fst
    (List.sort
     (fun b1 b2 -> snd (unloc (snd b1)) - snd (unloc (snd b2)))
     bindings) in
  List.combine idents args

let initial_state_id_of_states (states : state_tyd IdMap.t) : symbol =
  fst
  (List.hd
   (IdMap.bindings
    (IdMap.filter (fun _ state -> (unloc state).is_initial) states)))

type party_body_tyd =
  {serves : symbol list located list;  (* what interfaces served by party *)
   states : state_tyd IdMap.t}         (* state machine *)

type party_tyd = party_body_tyd located  (* typed party *)

let state_of_party_tyd (pt : party_tyd) (st : symbol) : state_tyd =
  IdMap.find st (unloc pt).states

let initial_state_id_of_party_tyd (pt : party_tyd) : symbol =
  initial_state_id_of_states ((unloc pt).states)

(* info of real functionality parameter or subfunctionality

   (root, id) is the name of the composite direct interface (for a
   parameter) or ideal functionality (for a subfunctionality)

   clone is the clone of root, in the root of the real functionality

   in the case of a parameter, the corresponding argument will
   be a functionality from the same clone *)

type porsf_info = symbol  (* root *)
                * symbol  (* id *)
                * symbol  (* clone of root *)

type real_fun_body_tyd =
  {params       : (porsf_info * int) IdMap.t;  (* porsf_info of composite direct
                                                  interfaces; index is
                                                  parameter number from 0 *)
   id_dir_inter : symbol;                      (* name of composite direct
                                                  interface - with same
                                                  root *)
   id_adv_inter : symbol option;               (* optional name of composite
                                                  adversarial interface -
                                                  with same root *)
   sub_funs     : porsf_info IdMap.t;          (* porsf_info of ideal
                                                  functionalities - pair
                                                  is (root, id) *)
   parties      : party_tyd IdMap.t}           (* parties *)

type ideal_fun_body_tyd =
  {id_dir_inter : symbol;             (* name of composite direct interface -
                                         with same root *)
   id_adv_inter : symbol option;      (* optional name of basic adversarial
                                         interface - with same root *)
   states       : state_tyd IdMap.t}  (* state machine *)

type fun_body_tyd =
  | FunBodyRealTyd  of real_fun_body_tyd
  | FunBodyIdealTyd of ideal_fun_body_tyd

let real_fun_body_tyd_of (fbt : fun_body_tyd) : real_fun_body_tyd =
  match fbt with
  | FunBodyRealTyd rfbt -> rfbt
  | FunBodyIdealTyd _   -> failure "cannot happen"

let ideal_fun_body_tyd_of (fbt : fun_body_tyd) : ideal_fun_body_tyd =
  match fbt with
  | FunBodyRealTyd _     ->  failure "cannot happen"
  | FunBodyIdealTyd ifbt -> ifbt

let is_real_fun_body_tyd (fbt : fun_body_tyd) : bool =
  match fbt with
  | FunBodyRealTyd _  -> true
  | FunBodyIdealTyd _ -> false

let is_ideal_fun_body_tyd (fbt : fun_body_tyd) : bool =
  match fbt with
  | FunBodyRealTyd _  -> false
  | FunBodyIdealTyd _ -> true

let id_dir_inter_of_fun_body_tyd (fbt : fun_body_tyd) : symbol =
  match fbt with
  | FunBodyRealTyd rfbt  -> rfbt.id_dir_inter
  | FunBodyIdealTyd rfbi -> rfbi.id_dir_inter

let id_adv_inter_of_fun_body_tyd (fbt : fun_body_tyd) : symbol option =
  match fbt with
  | FunBodyRealTyd rfbt  -> rfbt.id_adv_inter
  | FunBodyIdealTyd ifbt -> ifbt.id_adv_inter

type fun_tyd = fun_body_tyd located  (* functionality *)

let is_real_fun_tyd (ft : fun_tyd) : bool =
  is_real_fun_body_tyd (unloc ft)

let is_ideal_fun_tyd (ft : fun_tyd) : bool =
  is_ideal_fun_body_tyd (unloc ft)

let id_dir_inter_of_fun_tyd (ft : fun_tyd) : symbol =
  id_dir_inter_of_fun_body_tyd (unloc ft)

let id_adv_inter_of_fun_tyd (ft : fun_tyd) : symbol option =
  id_adv_inter_of_fun_body_tyd (unloc ft)

let num_sub_funs_of_real_fun_tyd (ft : fun_tyd) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.cardinal rfbt.sub_funs

let is_sub_fun_of_real_fun_tyd (ft : fun_tyd) (sym : symbol) : bool =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.mem sym rfbt.sub_funs

let sub_fun_ord_of_real_fun_tyd (ft : fun_tyd) (subf : symbol) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.sub_funs in
  fst (List.findi (fun _ (q, _) -> q = subf) bndgs)

let sub_fun_ord_of_real_fun_tyd (ft : fun_tyd) (subf : symbol) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.sub_funs in
  fst (List.findi (fun _ (q, _) -> q = subf) bndgs)

let sub_fun_porsf_info_of_real_fun_tyd (ft : fun_tyd)
    (subf : symbol) : porsf_info =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.find subf rfbt.sub_funs

let sub_fun_name_nth_of_real_fun_tyd (ft : fun_tyd) (n : int) : symbol =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.sub_funs in
  fst (List.nth bndgs n)

let sub_fun_porsf_info_nth_of_real_fun_tyd (ft : fun_tyd)
    (n : int) : porsf_info =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.sub_funs in
  snd (List.nth bndgs n)

let sub_fun_sp_nth_of_real_fun_tyd (ft : fun_tyd)
    (n : int) : symb_pair =
  let (root, id, _) = sub_fun_porsf_info_nth_of_real_fun_tyd ft n in
  (root, id)

let num_params_of_real_fun_tyd (ft : fun_tyd) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.cardinal rfbt.params

let is_param_of_real_fun_tyd (ft : fun_tyd) (sym : symbol) : bool =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.mem sym rfbt.params

let param_name_nth_of_real_fun_tyd (ft : fun_tyd) (n : int) : symbol =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  fst (List.nth (indexed_map_to_list_keep_keys rfbt.params) n)

let porsf_info_dir_inter_of_param_of_real_fun_tyd
    (ft : fun_tyd) (param : symbol) : porsf_info =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  fst (IdMap.find param rfbt.params)

let index_of_param_of_real_fun_tyd (ft : fun_tyd) (param : symbol) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  snd (IdMap.find param rfbt.params)

let party_of_real_fun_tyd (ft : fun_tyd) (pty : symbol) : party_tyd =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.find pty rfbt.parties

let num_parties_of_real_fun_tyd (ft : fun_tyd) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.cardinal rfbt.parties

let party_ord_of_real_fun_tyd (ft : fun_tyd) (pty : symbol) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.parties in
  fst (List.findi (fun _ (q, _) -> q = pty) bndgs)

let party_nth_name_of_real_fun_tyd (ft : fun_tyd) (n : int) : symbol =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.parties in
  fst (List.nth bndgs n)

let party_nth_def_of_real_fun_tyd (ft : fun_tyd) (n : int) =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let bndgs = IdMap.bindings rfbt.parties in
  snd (List.nth bndgs n)

let initial_state_id_of_ideal_fun_tyd (ft : fun_tyd) : symbol =
  let states = (ideal_fun_body_tyd_of (unloc ft)).states in
  initial_state_id_of_states states

type sim_body_tyd =
  {uses : symbol;                (* basic adversarial interface
                                    from ideal functionality - with
                                    same root *)
   sims : symbol;                (* real functionality being
                                    simulated - with same root *)
   sims_args : porsf_info list;  (* arguments to real
                                    functionality - triples
                                    (cloned, id, clone), naming ideal
                                    functionalities (cloned, id) from
                                    clone clone *)
   states : state_tyd IdMap.t}   (* state machine *)

type sim_tyd = sim_body_tyd located  (* simulator *)

let initial_state_id_of_sim_tyd (st : sim_tyd) : symbol =
  let states = (unloc st).states in
  initial_state_id_of_states states

(* information about EC and UC clones *)

type sc_uc_used_by =
  | SC_UC_SubFun of int  (* UC clone used by nth (from 0) sub-functionality *)
  | SC_UC_Param  of int  (* UC clone used by nth (from 0) parameter *)

type sc_uc_clone_info =
  {sc_uc_as       : symbol;                    (* name of clone *)
   sc_uc_of       : symbol;                    (* root being cloned *)
   sc_uc_ppna_fun : string -> string -> ppna;  (* when given s and t, returns
                                                  ppna for formatting EC
                                                  expression of UC clone
                                                  augmented with overriding:
                                                  op s <- t *)
   sc_uc_used     : (string *                  (* real funct using clone *)
                     sc_uc_used_by)            (* how rf uses clone *)
                    option;
   sc_uc_loc      : EcLocation.t}

type spec_clone_info =
  | SCI_EC of ppna              (* ppna for formatting an EC clone *)
  | SCI_UC of sc_uc_clone_info  (* information about a UC clone *)

let sci_lookup_uc_clone (name : symbol) (scis : spec_clone_info list)
      : symbol option =
  let rec lookup scis =
    match scis with
    | []          -> None
    | sci :: scis ->
        match sci with
        | SCI_EC _    -> lookup scis
        | SCI_UC info ->
            if info.sc_uc_as = name
            then Some info.sc_uc_of
            else lookup scis in
  lookup scis

exception SCIUndefined
exception SCIAlreadyUsed

let sci_update_uc_clone_usage (name : symbol) (used : string * sc_uc_used_by)
    (scis : spec_clone_info list)
      : spec_clone_info list *
        symbol               *  (* uc_of corresponding to uc_as *)
        int =                   (* index from 0 of updated element *)
  let rec update i olds news =
    match news with
    | []        -> raise SCIUndefined
    | nw :: nws ->
        match nw with
        | SCI_EC _    -> update (i + 1) (olds @ [nw]) nws
        | SCI_UC info ->
            if info.sc_uc_as = name
            then match info.sc_uc_used with
                 | None ->
                     (olds @
                      [SCI_UC {info with sc_uc_used = Some used}] @
                      nws,
                      info.sc_uc_of,
                      i)
                 | Some _ -> raise SCIAlreadyUsed
            else update (i + 1) (olds @ [nw]) nws in
  update 0 [] scis

let rec sci_unused_first_clone (scis : spec_clone_info list)
    : (symbol * EcLocation.t) option =
  match scis with
  | []          -> None
  | sci :: scis ->
      match sci with
      | SCI_EC _    -> sci_unused_first_clone scis
      | SCI_UC info ->
          if Option.is_none info.sc_uc_used
          then Some (info.sc_uc_as, info.sc_uc_loc)
          else sci_unused_first_clone scis

(* four identifer pair (more precisely, pairs of symbols, the first of
   which is a root) maps for direct and adversarial interfaces,
   functionalities and simulators; their domains are disjoint; type
   arguments to IdPairMap.t are all located types

   five identifier maps indexed by roots, giving: UC and EC
   requires; ppna's for formatting spec parameters of roots;
   lists of clones of roots; and scopes of roots *)

type maps_tyd =
  {dir_inter_map   : inter_tyd IdPairMap.t;           (* direct interfaces *)
   adv_inter_map   : inter_tyd IdPairMap.t;           (* adversarial
                                                         interfaces *)
   fun_map         : fun_tyd IdPairMap.t;             (* functionalities *)
   sim_map         : sim_tyd IdPairMap.t;             (* simulators *)
   uc_reqs_map     : (symbol list) IdMap.t;           (* UC requires of roots *)
   ec_reqs_map     : ((symbol * bool) list) IdMap.t;  (* EC requires of roots *)
   spec_params_map : ppna IdMap.t;                    (* ppna's for formatting
                                                         spec parameters
                                                         of roots *)
   spec_clones_map : spec_clone_info list IdMap.t;    (* lists of clones
                                                         of roots *)
   ec_scope_map    : EcScope.scope IdMap.t}           (* scopes of roots *)

let exists_id_pair_maps_tyd
    (maps : maps_tyd) (id_pair : symb_pair) : bool =
  exists_id_pair maps.dir_inter_map id_pair ||
  exists_id_pair maps.adv_inter_map id_pair ||
  exists_id_pair maps.fun_map id_pair       ||
  exists_id_pair maps.sim_map id_pair

let exists_id_pair_inter_maps
    (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (id_pair : symb_pair) : bool =
  exists_id_pair dir_inter_map id_pair ||
  exists_id_pair adv_inter_map id_pair

type msg_mode =  (* message mode *)
  | Dir
  | Adv

let get_inter_tyd_mode (maps : maps_tyd) (root : symbol) (top : symbol)
      : (msg_mode * inter_tyd) option =
  match IdPairMap.find_opt (root, top) maps.dir_inter_map with
  | None    ->
      (match IdPairMap.find_opt (root, top) maps.adv_inter_map with
       | None    -> None
       | Some it -> Some (Adv, it))
  | Some it -> Some (Dir, it)

let get_inter_tyd (maps : maps_tyd) (root : symbol) (top : symbol)
      : inter_tyd option =
  match get_inter_tyd_mode maps root top with
  | None         -> None
  | Some (_, it) -> Some it

let inter_names (root : symbol) (maps : maps_tyd) : IdSet.t =
  let i_n (map : inter_tyd IdPairMap.t) =
    IdSet.of_list
    (List.filter_map
     (fun (id_pr, _) ->
        if fst id_pr = root
        then Some (snd id_pr)
        else None)
     (IdPairMap.bindings map)) in
  IdSet.union (i_n maps.dir_inter_map) (i_n maps.adv_inter_map)

let real_fun_names (root : symbol) (maps : maps_tyd) : IdSet.t =
  IdSet.of_list
  (List.filter_map
   (fun (id_pr, ft) ->
      if fst id_pr = root && is_real_fun_body_tyd (unloc ft)
      then Some (snd id_pr)
      else None)
   (IdPairMap.bindings maps.fun_map))

let ideal_fun_names (root : symbol) (maps : maps_tyd) : IdSet.t =
  IdSet.of_list
  (List.filter_map
   (fun (id_pr, ft) ->
      if fst id_pr = root && not (is_real_fun_body_tyd (unloc ft))
      then Some (snd id_pr)
      else None)
   (IdPairMap.bindings maps.fun_map))

let sim_names (root : symbol) (maps : maps_tyd) : IdSet.t =
  IdSet.of_list
  (List.filter_map
   (fun (id_pr, _) ->
      if fst id_pr = root
      then Some (snd id_pr)
      else None)
   (IdPairMap.bindings maps.sim_map))

(* for units checking *)

let is_singleton_unit (root : symbol) (maps : maps_tyd) : bool =
    let rf_names  = real_fun_names root maps in
    let if_names  = ideal_fun_names root maps in
    let sim_names = sim_names root maps in
    IdSet.cardinal rf_names  = 0 &&
    IdSet.cardinal if_names  = 1 &&
    IdSet.cardinal sim_names = 0

let is_triple_unit (root : symbol) (maps : maps_tyd) : bool =
    let rf_names  = real_fun_names root maps in
    let if_names  = ideal_fun_names root maps in
    let sim_names = sim_names root maps in
    IdSet.cardinal rf_names  = 1 &&
    IdSet.cardinal if_names  = 1 &&
    IdSet.cardinal sim_names = 1

(* interface names that are reachable from an interface *)

let inter_names_reach_inter
    (root : symbol) (maps : maps_tyd) (id : symbol) : IdSet.t =
  let reach (map : inter_tyd IdPairMap.t) : IdSet.t =
    match IdPairMap.find_opt (root, id) map with
    | None    -> IdSet.empty
    | Some it ->
        match unloc it with
        | BasicTyd _      -> IdSet.empty
        | CompositeTyd mp ->
            IdSet.of_list (List.map snd (IdMap.bindings mp)) in
  IdSet.union
  (IdSet.singleton id)  (* include original id *)
  (IdSet.union
   (reach maps.dir_inter_map)  (* only one will be non-empty *)
   (reach maps.adv_inter_map))

(* interface names that are reachable from a functionality *)

let inter_names_reach_fun
    (root : symbol) (maps : maps_tyd) (id : symbol) : IdSet.t =
  match unloc (IdPairMap.find (root, id) maps.fun_map) with
  | FunBodyRealTyd rfbt  ->
      IdSet.union
      (inter_names_reach_inter root maps rfbt.id_dir_inter)
      (match rfbt.id_adv_inter with
       | None        -> IdSet.empty
       | Some adv_id -> inter_names_reach_inter root maps adv_id)
  | FunBodyIdealTyd ifbt ->
      IdSet.union
      (inter_names_reach_inter root maps ifbt.id_dir_inter)
      (omap_dfl IdSet.singleton IdSet.empty
       ifbt.id_adv_inter)  (* will be basic, if exists *)

(* interface names that are reachable from a simulator *)

let inter_names_reach_sim
    (root : symbol) (maps : maps_tyd) (id : symbol) : IdSet.t =
  let sbt = unloc (IdPairMap.find (root, id) maps.sim_map) in
  IdSet.singleton sbt.uses  (* will be basic *)
  (* the interfaces reachable from the real functionality it
     simulates will be collected via that real functionality *)

let basic_adv_inter_names_of_real_fun
    (root : symbol) (maps : maps_tyd) (id : symbol) : IdSet.t =
  match unloc (IdPairMap.find (root, id) maps.fun_map) with
  | FunBodyRealTyd rfbt  ->
      (match rfbt.id_adv_inter with
       | None        -> IdSet.empty
       | Some adv_id ->
           match unloc (IdPairMap.find (root, adv_id) maps.adv_inter_map) with
           | BasicTyd _      -> failure "cannot happen"
           | CompositeTyd mp ->
               (IdSet.of_list (List.map snd (IdMap.bindings mp))))
  | FunBodyIdealTyd _    -> failure "cannot happen"

(* assuming units checking has been performed *)

let roots_of_map (map : 'a IdPairMap.t) : IdSet.t =
  IdSet.of_list (List.map (fst |- fst) (IdPairMap.bindings map))

let roots_of_maps (maps : maps_tyd) : IdSet.t =
  let roots1 =
    IdSet.union (roots_of_map maps.dir_inter_map)
    (IdSet.union (roots_of_map maps.adv_inter_map)
     (IdSet.union (roots_of_map maps.fun_map) (roots_of_map maps.sim_map))) in
  let roots2 =
    IdSet.of_list (List.map fst (IdMap.bindings maps.uc_reqs_map)) in
  let roots3 =
    IdSet.of_list (List.map fst (IdMap.bindings maps.ec_reqs_map)) in
  let roots4 =
    IdSet.of_list (List.map fst (IdMap.bindings maps.ec_scope_map)) in
  assert (IdSet.equal roots1 roots2 && IdSet.equal roots2 roots3 &&
          IdSet.equal roots3 roots4);
  roots1

type singleton_info =
  {si_root          : symbol;
   si_ideal         : symbol;
   si_comp_dir      : symbol;
   si_basic_adv_opt : symbol option}

type triple_info =
  {ti_root             : symbol;
   ti_real             : symbol;
   ti_ideal            : symbol;
   ti_sim              : symbol;
   ti_comp_dir         : symbol;
   ti_comp_adv_opt     : symbol option;
   ti_if_sim_basic_adv : symbol;
   ti_sims             : porsf_info list;
   ti_num_adv_pis      : int}

type unit_info =
  | UI_Singleton of singleton_info
  | UI_Triple    of triple_info

let is_singleton_unit_info (ui : unit_info) : bool =
  match ui with
  | UI_Singleton _ -> true
  | UI_Triple _    -> false

let is_triple_unit_info (ui : unit_info) : bool =
  match ui with
  | UI_Singleton _ -> false
  | UI_Triple _    -> true

let num_adv_pis_of_parties_of_real_fun
    (maps : maps_tyd) (root : symbol) (ft : fun_tyd) : int =
  match id_adv_inter_of_fun_tyd ft with
  | None      -> 0
  | Some comp ->
      (let ibt =
         unloc (IdPairMap.find (root, comp) maps.adv_inter_map) in
       match ibt with
       | BasicTyd _       -> failure "cannot happen"
       | CompositeTyd map -> IdMap.cardinal map)

(* even if a subfunctionality has no adversarial interface, we
   still allocate an adversarial port index for it *)

let num_adv_pis_of_sub_funs_of_real_fun (ft : fun_tyd) : int =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  IdMap.cardinal rfbt.sub_funs

let unit_info_of_root (maps : maps_tyd) (root : symbol) : unit_info =
  let rf_names = real_fun_names root maps in
  let if_names = ideal_fun_names root maps in
  let sim_names = sim_names root maps in
  if IdSet.cardinal rf_names = 0
  then let if_name = sing_elt_of_id_set if_names in
       let ift = IdPairMap.find (root, if_name) maps.fun_map in
      UI_Singleton
      {si_root          = root;
       si_ideal         = if_name;
       si_comp_dir      = id_dir_inter_of_fun_tyd ift;
       si_basic_adv_opt = id_adv_inter_of_fun_tyd ift}
  else let if_name = sing_elt_of_id_set if_names in
       let ift = IdPairMap.find (root, if_name) maps.fun_map in
       let rf_name = sing_elt_of_id_set rf_names in
       let rft = IdPairMap.find (root, rf_name) maps.fun_map in
       let sim_name = sing_elt_of_id_set sim_names in
       let sbt = unloc (IdPairMap.find (root, sim_name) maps.sim_map) in
       let num_adv_pis_of_parties =
         num_adv_pis_of_parties_of_real_fun maps root rft in
       let num_adv_pis_of_sub_funs = num_adv_pis_of_sub_funs_of_real_fun rft in
       let num_adv_pis =
         1 + num_adv_pis_of_parties + num_adv_pis_of_sub_funs in
       UI_Triple
       {ti_root             = root;
        ti_real             = rf_name;
        ti_ideal            = if_name;
        ti_sim              = sim_name;
        ti_comp_dir         = id_dir_inter_of_fun_tyd ift;
        ti_comp_adv_opt     = id_adv_inter_of_fun_tyd rft;
        ti_if_sim_basic_adv = Option.get (id_adv_inter_of_fun_tyd ift);
        ti_sims             = sbt.sims_args;
        ti_num_adv_pis      = num_adv_pis}

let is_basic_adv_of_ideal_fun_of_unit (uior : unit_info) (bas : symbol) : bool =
  match uior with
  | UI_Singleton si -> si.si_basic_adv_opt = Some bas
  | UI_Triple ti    -> ti.ti_if_sim_basic_adv = bas

let basic_adv_of_ideal_fun_of_triple_unit (uior : unit_info) : symbol =
  match uior with
  | UI_Singleton _ -> failure "should not happen"
  | UI_Triple ti   -> ti.ti_if_sim_basic_adv

let get_dir_sub_inter_of_party_of_real_fun (ft : fun_tyd) (pty : symbol)
      : symbol option =
  try
    let dir_comp = id_dir_inter_of_fun_tyd ft in
    let party = unloc (party_of_real_fun_tyd ft pty) in
    let serves = party.serves in
    (some -| List.hd -| List.tl -| unloc)
    (List.find
     (fun x -> List.hd (unloc x) = dir_comp)
     serves)
  with _ -> None

let get_adv_sub_inter_of_party_of_real_fun (ft : fun_tyd) (pty : symbol)
      : symbol option =
  try
    let adv_comp = oget (id_adv_inter_of_fun_tyd ft) in
    let party = unloc (party_of_real_fun_tyd ft pty) in
    let serves = party.serves in
    (some -| List.hd -| List.tl -| unloc)
    (List.find
     (fun x -> List.hd (unloc x) = adv_comp)
     serves)
  with _ -> None

(* None if the party does not serve a basic direct interface;
   otherwise Some (comp, sub, i), where [comp; sub] is the basic
   direct interface served by the party, and i is the port index for
   direct messages to/from the party *)

type party_dir_info = (symbol * symbol * int) option

let get_dir_info_of_party_of_real_fun
    (maps : maps_tyd) (root : symbol) (ft : fun_tyd)
    (pty : symbol) : party_dir_info =
  match get_dir_sub_inter_of_party_of_real_fun ft pty with
  | None     -> None
  | Some sub ->
      let comp = id_dir_inter_of_fun_tyd ft in
      let ibt = unloc (IdPairMap.find (root, comp) maps.dir_inter_map) in
      match ibt with
      | BasicTyd _       -> failure "cannot happen"
      | CompositeTyd map ->
        Some (comp, sub, id_map_ordinal1_of_sym map sub)

(* None if the party does not serve a basic adversarial interface;
   otherwise Some (comp, sub, i, j), where [comp; sub] is the basic
   direct interface served by the party, and i is the port index for
   adversarial messages to/from the party, and j is the corresponding
   adversarial port index *)

type party_adv_info = (symbol * symbol * int * int) option

let get_adv_info_of_party_of_real_fun
    (maps : maps_tyd) (root : symbol) (base : int) (ft : fun_tyd)
    (pty : symbol) : party_adv_info =
  match get_adv_sub_inter_of_party_of_real_fun ft pty with
  | None     -> None
  | Some sub ->
      let comp = oget (id_adv_inter_of_fun_tyd ft) in
      let ibt =
        unloc (IdPairMap.find (root, comp) maps.adv_inter_map) in
        match ibt with
        | BasicTyd _       -> failure "cannot happen"
        | CompositeTyd map ->
            let n = id_map_ordinal_of_sym map sub in
            Some (comp, sub, 1 + n, base + 1 + n)

let get_internal_pi_of_party_of_real_fun (ft : fun_tyd) (pty : symbol) : int =
  1 + party_ord_of_real_fun_tyd ft pty

type party_info = {
  pi_pdi : party_dir_info;  (* direct info for party *)
  pi_pai : party_adv_info;  (* adversarial info for party *)
  pi_ipi : int              (* internal port index *)
}

let get_info_of_party (maps : maps_tyd) (root : symbol) (base : int)
    (ft : fun_tyd) (pty : symbol) : party_info =
  let dir_opt = get_dir_info_of_party_of_real_fun maps root ft pty in
  let adv_opt = get_adv_info_of_party_of_real_fun maps root base ft pty in
  let intern_pi = get_internal_pi_of_party_of_real_fun ft pty in
  {pi_pdi = dir_opt; pi_pai = adv_opt; pi_ipi = intern_pi}

type real_fun_info = party_info IdMap.t  (* map from party ids *)

let get_info_of_real_func (maps : maps_tyd) (root : symbol) (base : int)
    (ft : fun_tyd) : real_fun_info =
  let rfbt = real_fun_body_tyd_of (unloc ft) in
  let party_infos =
    List.map
    (fun pty -> (pty, get_info_of_party maps root base ft pty))
    (List.map fst (IdMap.bindings rfbt.parties)) in
  List.fold_left
  (fun mp (pty, pty_info) -> IdMap.add pty pty_info mp)
  IdMap.empty party_infos

(* returns the adversarial port index of the nth (counting from 0, in
   the ordering of the subfunctionality names) subfunctionality of a
   real functionality *)

let get_adv_pi_of_nth_sub_fun_of_real_fun
    (maps : maps_tyd) (root : symbol) (base : int)
    (ft : fun_tyd) (n : int) : int =
  let num_adv_pis_of_parties =
    num_adv_pis_of_parties_of_real_fun maps root ft in
  base + 1 + num_adv_pis_of_parties + n

(* check that a composite interface is valid and has the given
   sub interface, returning None when this is not true, and
   Some of the port index of the sub interface otherwise *)

let check_sub_interface_and_get_pi (maps : maps_tyd) (root : symbol)
    (comp : symbol) (sub : symbol) : int option =
  match get_inter_tyd maps root comp with
  | None    -> None
  | Some it ->
      match unloc it with
      | BasicTyd _       -> None
      | CompositeTyd map -> Some (id_map_ordinal1_of_sym map sub)

(* get the port index of a sub interface of a composite interface *)

let get_pi_of_sub_interface (maps : maps_tyd) (root : symbol)
    (comp : symbol) (sub : symbol) : int =
  match check_sub_interface_and_get_pi maps root comp sub with
  | None   -> failure "should not happen"
  | Some i -> i

(* get the child index (used as the suffix of the address) plus the
   porsf_info of the composite direct interface of a parameter or
   subfunctionality of a real functionality; returns None when top is
   neither parameter nor subfunctionality *)

let get_child_index_and_comp_inter_sp_of_param_or_sub_fun_of_real_fun
    (maps : maps_tyd) (ft : fun_tyd) (top : symbol)
      : (int * symb_pair) option =
  match (try Some (index_of_param_of_real_fun_tyd ft top) with
         | _ -> None) with
  | Some i ->
      let (root, id, _) =
        porsf_info_dir_inter_of_param_of_real_fun_tyd ft top in
      Some (i + 1, (root, id))
  | None   ->
      match (try Some (sub_fun_ord_of_real_fun_tyd ft top) with
             | _ -> None) with
    | Some i ->
        let (root, id, _) = sub_fun_porsf_info_of_real_fun_tyd ft top in
        let sub_fun_ft = IdPairMap.find (root, id) maps.fun_map in
        let id_dir = (root, id_dir_inter_of_fun_tyd sub_fun_ft) in
        Some (i + num_params_of_real_fun_tyd ft + 1, id_dir)
    | None   -> None

(* Interpreter User Input *)

(* typed functionality expression

   each functionality is qualified by its root file

   the path is of the theory the functionality's body should be
   interpreted in *)

type fun_expr_tyd =
  | FunExprTydReal  of symb_pair * symbol list * fun_expr_tyd list
  | FunExprTydIdeal of symb_pair * symbol list

let is_real_at_top_fet (fet : fun_expr_tyd) : bool =
  match fet with
  | FunExprTydReal _  -> true
  | FunExprTydIdeal _ -> false

let is_ideal_at_top_fet (fet : fun_expr_tyd) : bool =
  match fet with
  | FunExprTydReal _  -> false
  | FunExprTydIdeal _ -> true

(* typed expression for message in transit

   the message path must be root-qualified *)

type sent_msg_expr_ord_tyd = {
  mode           : msg_mode;    (* message mode *)
  dir            : msg_dir;     (* message direction *)
  src_port_form  : form;        (* source *)
  path           : msg_path_u;  (* message path *)
  args           : form list;   (* message arguments *)
  dest_port_form : form         (* destination *)
}

let drop_root_of_msg_path_u (path : msg_path_u) : msg_path_u =
  let {inter_id_path = iip; msg = msg} = path in
  {inter_id_path = List.tl iip; msg = msg}

let drop_head_of_msg_path_in_sent_msg_expr_ord_tyd (sme : sent_msg_expr_ord_tyd)
      : sent_msg_expr_ord_tyd =
  {sme with path = drop_root_of_msg_path_u sme.path}

let subst_comp_and_drop_root_in_msg_path_u (path : msg_path_u)
    (old_comp : symbol) (new_comp : symbol) : msg_path_u option =
  let {inter_id_path = iip; msg = msg} = path in
  match iip with
  | [_; comp; sub] ->
      if comp = old_comp
      then Some {inter_id_path = [new_comp; sub]; msg = msg}
      else None
  | _              -> None

let subst_comp_and_drop_root_in_sent_msg_expr_ord_tyd
    (sme : sent_msg_expr_ord_tyd) (old_comp : symbol)
    (new_comp : symbol) : sent_msg_expr_ord_tyd option =
  match subst_comp_and_drop_root_in_msg_path_u sme.path old_comp new_comp with
  | None      -> None
  | Some path -> Some {sme with path = path}

let subst_for_iip_in_msg_path_u (path : msg_path_u) (new_iip : string list)
      : msg_path_u =
  {inter_id_path = new_iip; msg = path.msg}

let subst_for_iip_in_sent_msg_expr_ord_tyd
    (sme : sent_msg_expr_ord_tyd) (new_iip : string list)
      : sent_msg_expr_ord_tyd =
  let new_path = subst_for_iip_in_msg_path_u sme.path new_iip in
  {sme with path = new_path}

let check_and_subst_for_iip_in_msg_path_u (path : msg_path_u)
    (expected_iip : string list) (new_iip : string list)
      : msg_path_u option =
  let {inter_id_path = iip; msg = msg} = path in
  if iip = expected_iip
  then Some {inter_id_path = new_iip; msg = msg}
  else None

let check_and_subst_for_iip_in_sent_msg_expr_ord_tyd
    (sme : sent_msg_expr_ord_tyd) (expected_iip : string list)
    (new_iip : string list) : sent_msg_expr_ord_tyd option =
  match check_and_subst_for_iip_in_msg_path_u sme.path expected_iip new_iip with
  | None      -> None
  | Some path -> Some {sme with path = path}

type sent_msg_expr_env_adv_tyd = {  (* mode is implicitly Adv *)
  src_port_form  : form;
  dest_port_form : form
}

type sent_msg_expr_tyd =
  | SMET_Ord    of sent_msg_expr_ord_tyd
  | SMET_EnvAdv of sent_msg_expr_env_adv_tyd

let is_ord_sent_msg_expr_tyd (sme : sent_msg_expr_tyd) : bool =
  match sme with
  | SMET_Ord _    -> true
  | SMET_EnvAdv _ -> false

let is_env_adv_sent_msg_expr_tyd (sme : sent_msg_expr_tyd) : bool =
  match sme with
  | SMET_Ord _    -> false
  | SMET_EnvAdv _ -> true

let ord_of_sent_msg_expr_tyd (sme : sent_msg_expr_tyd)
      : sent_msg_expr_ord_tyd =
  match sme with
  | SMET_Ord ord  -> ord
  | SMET_EnvAdv _ -> failure "should not happen"

let env_adv_of_sent_msg_expr_tyd (sme : sent_msg_expr_tyd)
      : sent_msg_expr_env_adv_tyd =
  match sme with
  | SMET_Ord _          -> failure "should not happen"
  | SMET_EnvAdv env_adv -> env_adv

let mode_of_sent_msg_expr_tyd (sme : sent_msg_expr_tyd) : msg_mode =
  match sme with
  | SMET_Ord ord  -> ord.mode
  | SMET_EnvAdv _ -> Adv

let source_port_of_sent_msg_expr_tyd (sme : sent_msg_expr_tyd) : form =
  match sme with
  | SMET_Ord ord        -> ord.src_port_form
  | SMET_EnvAdv env_adv -> env_adv.src_port_form

let dest_port_of_sent_msg_expr_tyd (sme : sent_msg_expr_tyd) : form =
  match sme with
  | SMET_Ord ord        -> ord.dest_port_form
  | SMET_EnvAdv env_adv -> env_adv.dest_port_form

let pp_form (env : EcEnv.env) (fmt : Format.formatter) (f : form) : unit =
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pp_form = EcPrinting.pp_form ppe in
  Format.fprintf fmt "@[%a@]"
  pp_form f

let pp_sent_msg_expr_tyd (env : EcEnv.env) (fmt : Format.formatter)
    (sme : sent_msg_expr_tyd) : unit =
  let no_parens (f : form) : bool =
    is_local f ||
    match f.f_node with
    | Fop (_, []) -> true
    | _           -> false in
  let pp_portform (fmt : Format.formatter) (f : form) : unit =
    if no_parens f
    then Format.fprintf fmt "%a" (pp_form env) f
    else Format.fprintf fmt "(@[%a@])" (pp_form env) f in
  match sme with
  | SMET_Ord sme    ->
      let inp, path, args, outp =
        sme.src_port_form, sme.path, sme.args, sme.dest_port_form in
      let pp_mpath (fmt : Format.formatter) (path : msg_path_u) : unit =
        let rec pp_strl (fmt : Format.formatter) (strl : string list) : unit =
          match strl with
          | []      -> Format.fprintf fmt ""
          | [s]     -> Format.fprintf fmt "%s." s
          | s :: tl -> Format.fprintf fmt "%s.%a" s pp_strl tl in
        Format.fprintf fmt "%a%s" pp_strl path.inter_id_path path.msg in
      let pp_forml (fmt : Format.formatter) (forml : form list) : unit =
        EcPrinting.pp_list ",@ " (pp_form env) fmt forml in
      let pp_args (fmt : Format.formatter) (forml : form list) : unit =
        if List.is_empty forml
        then ()
        else Format.fprintf fmt "(@[%a@])" pp_forml forml in
      Format.fprintf fmt "@[<hv>%a@@@,%a@,%a@,@@%a@]"
      pp_portform inp
      pp_mpath path
      pp_args args
      pp_portform outp
  | SMET_EnvAdv sme ->
      Format.fprintf fmt "@[%a@@_@,@@%a@]"
      pp_portform sme.src_port_form
      pp_portform sme.dest_port_form

(* pretty print a typed sent message expression to a string *)

let pp_sent_msg_expr_to_string (env : EcEnv.env)
    (sme : sent_msg_expr_tyd) : string =
  let _ = Format.flush_str_formatter () in
  let () = pp_sent_msg_expr_tyd env Format.str_formatter sme in
  Format.flush_str_formatter ()
