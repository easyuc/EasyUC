(* UcTypedSpec module *)

(* Typed Specifications *)

open EcLocation
open EcSymbols
open EcTypes
open UcSpecTypedSpecCommon

(* maps and sets *)

module IdMap = Map.Make(String)  (* domain: string = symbol *)
module IdSet = Set.Make(String)

(* we sometimes use "id" to stand for a symbol, and sometimes for a
   located symbol (in which case we may use "uid" to stand for the
   unlocated version) *)

let exists_id (id_map : 'a IdMap.t) (id : symbol) : bool = 
  IdMap.exists (fun key _ -> key = id) id_map

let id_map_domain (map : 'a IdMap.t) : IdSet.t =
  IdSet.of_list (List.map fst (IdMap.bindings map))

module SL =  (* domain: string list = symbol list *)
  struct
    type t = string list
    let compare = Stdlib.compare
  end

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
  let l = IdMap.fold (fun _ v l -> v :: l ) mapind [] in
  let lord = List.sort (fun a1 a2 -> snd a1 - snd a2) l in
  List.map (fun a -> fst a) lord

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

(* located type plus an index, starting from 0 *)

type ty_index = (ty * int) located

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

let is_basic_tyd ibt =
  match ibt with
  | BasicTyd _     -> true
  | CompositeTyd _ -> false

let is_composite_tyd ibt =
  match ibt with
  | BasicTyd _     -> false
  | CompositeTyd _ -> true

type inter_tyd = inter_body_tyd located  (* typed interface *)

(* state machines, typed functionalities and simulators *)

(* message and state expressions *)

type msg_expr_tyd =
  {path      : msg_path;           (* message path *)
   args      : expr list located;  (* message arguments *)
   port_expr : expr option}        (* message destination - port expr *)

type state_expr_tyd =
  {id   : psymbol;            (* state to transition to *)
   args : expr list located}  (* arguments of new state *)

(* instructions *)

type send_and_transition_tyd =
  {msg_expr   : msg_expr_tyd;    (* message to send *)
   state_expr : state_expr_tyd}  (* state to transition to *)

type bindings = ((EcIdent.t * EcTypes.ty) list)

type instruction_tyd_u =
  | Assign of lhs * expr                           (* ordinary assignment *)
  | Sample of lhs * expr                           (* sampling assignment *)
  | ITE of expr * instruction_tyd list located *   (* if-then-else *)
           instruction_tyd list located option
  | Match of expr * match_clause_tyd list located  (* match instruction *)
  | SendAndTransition of send_and_transition_tyd   (* send and transition *)
  | Fail                                           (* failure *)

and instruction_tyd = instruction_tyd_u located

and match_clause_tyd = symbol * (bindings * instruction_tyd list located)

type msg_match_clause_tyd =                 (* message match clause *)
  {msg_pat : msg_pat;                       (* message pattern *)
   code    : instruction_tyd list located}  (* code of clause *)

type state_body_tyd =
  {is_initial : bool;                       (* the initial state? *)
   params     : ty_index IdMap.t;           (* typed parameters, index is
                                               parameter number *)
   vars       : ty located IdMap.t;         (* local variables *)
   mmclauses  : msg_match_clause_tyd list}  (* message match clauses *)

type state_tyd = state_body_tyd located  (* typed state *)

type party_body_tyd =
  {serves : symbol list located list;  (* what interfaces served by party *)
   states : state_tyd IdMap.t}         (* state machine *)

type party_tyd = party_body_tyd located  (* typed party *)

type real_fun_body_tyd =
  {params       : (symb_pair * int) IdMap.t;  (* names of composite direct
                                                 interfaces; index is
                                                 parameter number *)
   id_dir_inter : symbol;                     (* name of composite direct
                                                 interface - with same
                                                 root *)
   id_adv_inter : symbol option;              (* optional name of composite
                                                 adversarial interface -
                                                 with same root *)
   sub_funs     : symb_pair IdMap.t;          (* names of ideal
                                                 functionalities - pair
                                                 is (root, id) *)
   parties      : party_tyd IdMap.t}          (* parties *)

type ideal_fun_body_tyd =
  {id_dir_inter : symbol;             (* name of composite direct interface -
                                         with same root *)
   id_adv_inter : symbol;             (* name of basic adversarial interface -
                                         with same root *)
   states       : state_tyd IdMap.t}  (* state machine *)

type fun_body_tyd =
  | FunBodyRealTyd  of real_fun_body_tyd
  | FunBodyIdealTyd of ideal_fun_body_tyd

let real_fun_body_tyd_of (fbt : fun_body_tyd) : real_fun_body_tyd =
  match fbt with
  | FunBodyRealTyd rfbt -> rfbt
  | FunBodyIdealTyd _   -> UcMessage.failure "cannot happen"

let ideal_fun_body_tyd_of (fbt : fun_body_tyd) : ideal_fun_body_tyd =
  match fbt with
  | FunBodyRealTyd _     ->  UcMessage.failure "cannot happen" 
  | FunBodyIdealTyd ifbt -> ifbt

let is_real_fun_body_tyd (fbt : fun_body_tyd) : bool =
  match fbt with
  | FunBodyRealTyd _  -> true
  | FunBodyIdealTyd _ -> false

let id_dir_inter_of_fun_body_tyd (fbt : fun_body_tyd) : symbol =
  match fbt with
  | FunBodyRealTyd fbr  -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

let id_adv_inter_of_fun_body_tyd (fbt : fun_body_tyd) : symbol option =
  match fbt with
  | FunBodyRealTyd fbr  -> fbr.id_adv_inter
  | FunBodyIdealTyd fbi -> Some fbi.id_adv_inter

type fun_tyd = fun_body_tyd located  (* functionality *)

type sim_body_tyd =
  {uses : symbol;                       (* basic adversarial interface
                                           from ideal functionality - with
                                           same root *)
   sims : symbol;                       (* real functionality being
                                           simulated - with same root *)
   sims_arg_pair_ids : symb_pair list;  (* arguments to real
                                           functionality - pairs
                                           (root, id), naming ideal
                                           functionalities *)
   states : state_tyd IdMap.t}          (* state machine *)

type sim_tyd = sim_body_tyd located  (* simulator *)

(* four identifer pair (more precisely, pairs of symbols) maps for
   direct and adversarial interfaces, functionalities and simulators;
   their domains are disjoint

   type arguments to IdPairMap.t are all located types *)

type maps_tyd =
  {dir_inter_map : inter_tyd IdPairMap.t;  (* direct interfaces *)
   adv_inter_map : inter_tyd IdPairMap.t;  (* adversarial interfaces *)
   fun_map       : fun_tyd IdPairMap.t;    (* functionalities *)
   sim_map       : sim_tyd IdPairMap.t}    (* simulators *)

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
      (IdSet.singleton ifbt.id_adv_inter)  (* will be basic *)

(* interface names that are reachable from a simulator *)

let inter_names_reach_sim
    (root : symbol) (maps : maps_tyd) (id : symbol) : IdSet.t =
  let sbt = unloc (IdPairMap.find (root, id) maps.sim_map) in
  IdSet.union
  (IdSet.singleton sbt.uses)  (* will be basic *)
  (inter_names_reach_fun root maps sbt.sims)

let basic_direct_inter_names_of_real_fun
    (root : symbol) (maps : maps_tyd) (id : symbol) : IdSet.t =
  match unloc (IdPairMap.find (root, id) maps.fun_map) with
  | FunBodyRealTyd rfbt  ->
      (match rfbt.id_adv_inter with
       | None        -> IdSet.empty
       | Some adv_id ->
           match unloc (IdPairMap.find (root, adv_id) maps.adv_inter_map) with
           | BasicTyd _      -> UcMessage.failure "cannot happen"
           | CompositeTyd mp ->
               (IdSet.of_list (List.map snd (IdMap.bindings mp))))
  | FunBodyIdealTyd _    -> UcMessage.failure "cannot happen"

(* typed top-level specifications *)

type typed_spec = maps_tyd
