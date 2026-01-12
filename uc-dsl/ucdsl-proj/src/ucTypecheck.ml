(* UcTypecheck module *)

(* Typecheck a specification or user input to the interpreter *)

open Batteries
open Format

open EcLocation
open EcSymbols
open EcParsetree
open EcAst
open EcTypes
open EcFol
open EcUnify
open EcTyping
open EcEnv

open UcUtils
open UcMessage
open UcSpec
open UcSpecTypedSpecCommon
open UcTypedSpec

(* the current maximum number of allowed parameters to a message;
   changing this will require updates to the EasyCrypt code generation *)

let max_msg_params = 8

(* convert a named list into an id map, checking for uniqueness
   of names; get_id returns the name of a list element *)

let check_unique_ids
    (msgf : formatter -> unit) (al : 'a list) (get_id : 'a -> psymbol)
      : 'a IdMap.t =
  let id_map = IdMap.empty in
  List.fold_left
  (fun id_map a ->
     let id_l = get_id a in
     if exists_id id_map (unloc id_l) then
       error_message (loc id_l)
       (fun ppf -> fprintf ppf "@[%t:@ %s@]" msgf (unloc id_l))
     else IdMap.add (unloc id_l) a id_map)
  id_map al

(* EasyCrypt type checks *)

let top_env () = UcEcInterface.env ()

let unif_env () = EcUnify.UniEnv.create None

let is_ec_theory_name s =
  Option.is_some (EcEnv.Theory.lookup_opt ([], s) (top_env ()))

let is_ec_type_name s =
  Option.is_some (EcEnv.Ty.lookup_opt ([], s) (top_env ()))

let is_ec_op_name s =
  Option.is_some (EcEnv.Op.lookup_opt ([], s) (top_env ()))

(* check type in top-level environment, rejecting type variables *)

let check_type_top (pty : pty) : ty =
  let ue = unif_env () in
  transty tp_nothing (top_env ()) ue pty

let check_name_type_bindings_top
    (msgf : formatter -> unit) (ntl : type_binding list)
      : ty_index IdMap.t =
  let nt_map = check_unique_ids msgf ntl (fun nt -> nt.id) in
  IdMap.map
  (fun (nt : type_binding) ->
     mk_loc (loc nt.id) (check_type_top nt.ty, index_of_ex nt ntl))
  nt_map

(****************************** interface checks ******************************)

type inter_kind =
  | DirectInterKind
  | AdversarialInterKind

let inter_kind_to_str art ik =
  match ik with
  | DirectInterKind      ->
      (if art then "a " else "") ^ "direct"
  | AdversarialInterKind ->
      (if art then "an " else "") ^ "adversarial"

let check_basic_inter (mds : message_def list) : inter_body_tyd =
  let msg_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ message@ name@]")
    mds (fun md -> md.id) in
  BasicTyd
  (IdMap.map
   (fun (md : message_def) ->
      if List.length md.params > max_msg_params
      then error_message (loc md.id)
           (fun ppf ->
              fprintf ppf
              ("@[more@ than@ the@ allowed@ maximum@ number@ (%d)@ of@ " ^^
               "parameters@]")
              max_msg_params)
      else let params_map =
                 check_name_type_bindings_top
                 (fun ppf ->
                    fprintf ppf "@[duplicate@ message@ parameter@ name@]")
                 md.params in
           let port =
                 Option.map
                 (fun idl ->
                    let id = unloc idl in
                    if IdMap.mem id params_map
                    then error_message (loc idl)
                         (fun ppf ->
                            fprintf ppf
                            "@[name@ also@ used@ as@ parameter@ name@]")
                    else id)
                 md.port in
           {dir        = md.dir;
            params_map = params_map;
            port       = port})
   msg_map)

let check_comp_item
    (ik : inter_kind) (root : symbol) (inter_map : inter_tyd IdPairMap.t)
    (ci : comp_item) : symbol =
  let uid = unloc ci.inter_id in
  match IdPairMap.find_opt (root, uid) inter_map with
  | None    ->
      error_message
      (loc ci.inter_id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ isn't@ %s@ interface@ name@]"
         uid (inter_kind_to_str true ik))
  | Some it ->
      let ibt = unloc it in
      if is_composite_tyd ibt
      then error_message (loc ci.inter_id)
           (fun ppf ->
              fprintf ppf
              "@[%s@ isn't@ a@ basic@ interface@]" uid)
      else unloc ci.inter_id

let check_comp_inter
    (ik : inter_kind) (root : symbol) (inter_map : inter_tyd IdPairMap.t)
    (cis : comp_item list) : inter_body_tyd =
  let comp_item_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ sub-interface@ name@]")
    cis (fun ci -> ci.sub_id) in
  CompositeTyd (IdMap.map (check_comp_item ik root inter_map) comp_item_map)

let check_inter
    (root : symbol) (e_maps : symb_pair -> bool) (ik : inter_kind)
    (inter_map : inter_tyd IdPairMap.t) (ni : named_inter)
      : inter_tyd IdPairMap.t =
  let uid = unloc ni.id in
  let () =
    if e_maps (root, uid)
    then error_message (loc ni.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let ibt =
    match ni.inter with
    | Basic mds     -> check_basic_inter mds
    | Composite cis -> check_comp_inter ik root inter_map cis in
  let it = mk_loc (loc ni.id) ibt in
  IdPairMap.add (root, uid) it inter_map

let check_inter_def
    (root : symbol) (maps : maps_tyd) (interd : inter_def) : maps_tyd =
  let e_maps = exists_id_pair_maps_tyd maps in
  match interd with
  | DirectInter ni      ->
      {maps with
         dir_inter_map =
           check_inter root e_maps DirectInterKind maps.dir_inter_map ni}
  | AdversarialInter ni ->
      {maps with
         adv_inter_map =
           check_inter root e_maps AdversarialInterKind maps.adv_inter_map ni}

let check_exists_inter_id
    (ik : inter_kind) (root : symbol) (inter_map : inter_tyd IdPairMap.t)
    (id : psymbol) : unit =
  let uid = unloc id in
  if exists_id_pair inter_map (root, uid) then ()
  else error_message (loc id)
       (fun ppf ->
          fprintf ppf
          "@[%s@ interface@ does@ not@ exist:@ %s@]"
          (inter_kind_to_str false ik) uid)

let check_is_basic_id
    (ik : inter_kind) (root : symbol) (inter_map : inter_tyd IdPairMap.t)
    (id : psymbol) : unit =
  let uid = unloc id in
  match unloc (IdPairMap.find (root, uid) inter_map) with
  | BasicTyd _     -> ()
  | CompositeTyd _ ->
      error_message (loc id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ interface@ must@ be@ basic:@ %s@]"
         (inter_kind_to_str false ik) uid)

let check_is_composite_id
    (ik : inter_kind) (root : symbol) (inter_map : inter_tyd IdPairMap.t)
    (id : psymbol) : unit =
  let uid = unloc id in
  match unloc (IdPairMap.find (root, uid) inter_map) with
  | BasicTyd _     ->
      error_message (loc id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ interface@ must@ be@ composite:@ %s@]"
         (inter_kind_to_str false ik) uid)
  | CompositeTyd _ -> ()

let check_exists_inter_qid
    (ik : inter_kind) (root : symbol) (inter_map : inter_tyd IdPairMap.t)
    (qid : pqsymbol) : symb_pair located =
  let uqid = unloc qid in
  let l = loc qid in
  match uqid with
  | ([], uid)   ->
      if exists_id_pair inter_map (root, uid)
      then mk_loc l (root, uid)
      else error_message l
           (fun ppf ->
              fprintf ppf
              "@[%s@ interface@ does@ not@ exist:@ %s@]"
              (inter_kind_to_str false ik) uid)
  | ([rt], uid) ->
      if exists_id_pair inter_map (rt, uid)
      then mk_loc l (rt, uid)
      else error_message l
           (fun ppf ->
              fprintf ppf
              "@[%s@ interface@ does@ not@ exist:@ %a@]"
              (inter_kind_to_str false ik) (pp_qsymbol_abbrev root) uqid)
  | _           ->
      error_message l
      (fun ppf ->
         fprintf ppf
         "@[invalid@ form@ for@ interface@ name:@ %a@]" pp_qsymbol uqid)

let check_is_basic_id_pair  (* currently not used *)
    (root : symbol) (ik : inter_kind) (inter_map : inter_tyd IdPairMap.t)
    (idp : symb_pair located) : unit =
  let uidp = unloc idp in
  let l = loc idp in
  match unloc (IdPairMap.find uidp inter_map) with
  | BasicTyd _     -> ()
  | CompositeTyd _ ->
      error_message l
      (fun ppf ->
         fprintf ppf
         "@[%s@ interface@ must@ be@ basic:@ %a@]"
         (inter_kind_to_str false ik) (pp_id_pair_abbrev root) uidp)

let check_is_composite_id_pair
    (root : symbol) (ik : inter_kind) (inter_map : inter_tyd IdPairMap.t)
    (idp : symb_pair located) : unit =
  let uidp = unloc idp in
  let l = loc idp in
  match unloc (IdPairMap.find uidp inter_map) with
  | BasicTyd _     ->
      error_message l
      (fun ppf ->
         fprintf ppf
         "@[%s@ interface@ must@ be@ composite:@ %a@]"
         (inter_kind_to_str false ik) (pp_id_pair_abbrev root) uidp)
  | CompositeTyd _ -> ()

(********************* functionality and simulator checks *********************)

(* the top-level check for states produces: *)

type state_body_mid =
  {is_initial : bool;                   (* the initial state? *)
   params     : ty_index IdMap.t;       (* typed parameters, index is
                                           parameter number *)
   vars       : ty located IdMap.t;     (* local variables *)
   mmclauses  : msg_match_clause list}  (* message match clauses *)

type state_mid = state_body_mid located

(* typechecking context for states

   state parameters and local variables are disjoint, and are lower
   identifiers; they are distinct from "envport", which can only
   be used in real and ideal functionalities (not simulators)

   in real functionalities, internal ports have the form [Party],
   where Party is the name of one of the functionality's parties; in
   simulators, internal ports have the form [RealFun; Party], where
   RealFun is the real functionality being simulated, and Party is one
   of its parties

   in the concrete syntax [Party] is written "intport Party", and
   [RealFun; Party] is written "intport RealFun.Party"; these are
   turned by the parser into PFident's, whose arguments are
   localizations of ([], "intport Party") and ([],
   "intport RealFun.Party")

   when internal ports are locally bound in environments, [Party] is
   turned into "intport Party", and [RealFun; Party] is turned into
   "intport RealFun.Party"

   when internal ports are turned into port indices (beginning at 1),
   we use the ordering List.compare String.compare; this is stable
   under the prepending of RealFun, so that [Party] in the real
   functionality and [RealFun; Party] in its simulator will be
   assigned the same port index *)

type kind =  (* kind of entity *)
  | RealPartyKind of bool  (* party of real functionality; bool is true iff
                              party serves basic adversarial interface *)
  | IdealKind              (* ideal functionality with adversarial interface *)
  | IdealNoAdvKind         (* ideal functionality no adversarial interface *)
  | SimKind                (* simulator *)

let is_real_kind (k : kind) : bool =
  match k with
  | RealPartyKind _ -> true
  | _               -> false

let is_ideal_kind (k : kind) : bool =
  match k with
  | IdealKind -> true
  | _         -> false

let is_ideal_no_adv_kind (k : kind) : bool =
  match k with
  | IdealNoAdvKind -> true
  | _              -> false

let is_sim_kind (k : kind) : bool =
  match k with
  | SimKind -> true
  | _       -> false

type state_context =
  {initial        : bool;                (* initial state? *)
   kind           : kind;                (* which kind of entity *)
   params         : ty_index Mid.t;      (* state parameters *)
   vars           :
     (EcIdent.t * ty) located IdMap.t;   (* map from variables to *)
                                         (* identifiers and types *)
   internal_ports : EcIdent.t QidMap.t}  (* map from internal ports
                                            to their identifiers *)

let make_state_context
    (s : state_body_mid) (ports : QidSet.t) (kind : kind) : state_context =
  let params =
    Mid.of_list
    (List.map
     (fun (x, u) ->
        (EcIdent.create x, u))
     (IdMap.bindings s.params)) in
  let vars =
    IdMap.mapi
    (fun k u ->
       mk_loc (loc u) (EcIdent.create k, unloc u))
    s.vars in
  let internal_ports =
    List.fold
    (fun acc qid ->
       QidMap.update qid
       (fun _ ->
          Some
          (EcIdent.create ("intport " ^ nonempty_qid_to_string qid)))
       acc)
    QidMap.empty
    (QidSet.elements ports) in
  {initial = s.is_initial; kind = kind; internal_ports = internal_ports;
   params = params; vars = vars}

(* static analysis information for states *)

type state_analysis =
  {uninit_vs : IdSet.t}  (* possibly uninitialized variables *)

let init_state_analysis (sc : state_context) : state_analysis =
  let un = IdSet.of_list (List.map fst (IdMap.bindings sc.vars)) in
  {uninit_vs = un}

let refine_state_analysis (sa : state_analysis) (id : symbol) =
  {sa with
     uninit_vs = IdSet.diff sa.uninit_vs (IdSet.singleton id) }

let merge_state_analysis (sa1 : state_analysis) (sa2 : state_analysis)
      : state_analysis =
  {uninit_vs = IdSet.union sa1.uninit_vs sa2.uninit_vs}

let merge_state_analyses (sas : state_analysis list) : state_analysis =
  match sas with
  | []        -> failure "cannot happen"
  | [sa]      -> sa
  | sa :: sas -> List.fold_left merge_state_analysis sa sas

(* envport is only defined in real and ideal functionalities: *)

let augment_env_with_state_context
    (env : EcEnv.env) (sc : state_context) : EcEnv.env =
    Var.bind_locals
    ((if sc.kind <> SimKind then [(envport_id, tfun port_ty tbool)] else []) @
     List.map
     (fun (_, id) -> (id, port_ty))
     (QidMap.bindings sc.internal_ports) @
     List.map (fun (id, u) -> (id, fst(unloc u))) (Mid.bindings sc.params) @
     List.map (fun (_, u) -> unloc u) (IdMap.bindings sc.vars))
    env

let bind_local_avoid_var
    (env : EcEnv.env) (sc : state_context) (ident : EcIdent.t) (ty : ty)
    (l : EcLocation.t) : EcEnv.env =
  if IdSet.mem (EcIdent.name ident) (vars_map_to_domain sc.vars)
  then error_message l
       (fun ppf ->
          fprintf ppf
          "@[bound@ identifier@ may@ not@ be@ program@ variable:@ %s@]"
          (EcIdent.name ident))
  else Var.bind_local ident ty env

let bind_locals_avoid_var
    (env : EcEnv.env) (sc : state_context) (bndgs : bindings) : EcEnv.env =
  List.fold_left
  (fun acc (id, ty) ->
     bind_local_avoid_var acc sc (unloc id) ty (loc id))
  env bndgs

(* state signatures - boolean saying if initial state or not, plus
   list of the types of each parameter of state *)

type state_sig = bool * ty list

let get_state_sig (s : state_body_mid) : state_sig =
  if s.is_initial then (true, [])
  else let ps = IdMap.bindings s.params in
       let ts = unlocs (snd (List.split ps)) in
       let tord = List.sort (fun t1 t2 -> snd t1 - snd t2) ts in
       (false, (fst (List.split tord)))

let get_state_sigs (states : state_mid IdMap.t) : state_sig IdMap.t =
  IdMap.map (fun s -> get_state_sig (unloc s)) states

(* a basic_inter_path will have the form (ids, b), where we call ids
   an inter id path:

   *** for real functionalities ***

   ids = [id1; id2], and id1 is the name of a composite interface the
   functionality implements, id2 is the name of one of that composite
   interface's sub-interfaces, and b is the basic interface (direct
   iff the composite interface is direct) corresponding (using the
   same root) to the interface name that id2 is associated with in the
   composite interface (possibly filtered to have only incoming or
   outgoing messages); or

   ids = [id1; id2], and id1 is the name of a parameter or
   subfunctionality of a real functionality, id2 is the name of one of
   the sub-interfaces of the composite direct interface implemented by
   the parameter or subfunctionality (in the case of a
   subfunctionality, the direct interface implemented by the ideal
   functionality the subfunctionality is an instance of), and b is the
   result of inverting the message directions (in -> out; out -> in)
   of the basic, direct interface corresponding to the interface name
   that id2 is associated with in the composite interface (possibly
   filtered to have only incoming or outgoing messages)

   *** for ideal functionalities ***

   ids = [id2], and id2 is the name of the adversarial basic interface
   the functionality implements, and b is that basic interface
   (possibly filtered to have only incoming or outgoing messages); or

   ids = [id1; id2], and id1 is the name of the composite direct
   interface the functionality implements, id2 is the name of one of
   that composite interface's sub-interfaces, and b is the basic
   direct interface corresponding to the interface name that id2 is
   associated with in the composite interface (possibly filtered to
   have only incoming or outgoing messages)

   *** for simulators ***

   ids = [id2], and id2 is the name of the adversarial basic interface
   the simulator uses, and b is that basic interface, where the
   directions of the messages have been inverted (possibly filtered to
   have only incoming or outgoing messages); or

   ids = [id1, id2, id3], and id1 is the name of the real
   functionality the simulator is simulating, id2 is the name of the
   composite adversarial interface that real functionality implements
   (this may not exist), id3 is the name of one of the sub-interfaces
   of id2, and b is the basic, adversarial interface corresponding to
   the interface name that id3 is associated with in the composite
   interface (possibly filtered to have only incoming or outgoing
   messages); or

   ids = [id1, id2, id3], and id1 is the name of the real
   functionality the simulator is simulating, id2 is the name of one
   of its subfunctionalities, id3 is the name of the adversarial basic
   interface of the ideal functionality that id2 is an instance of,
   and b is that basic interface (possibly filtered to have only
   incoming or outgoing message); or

   ids = [id1, id2, id3], and id1 is the name of the real
   functionality the simulator is simulating, id2 is the name of one
   of its parameters, id3 is the name of the adversarial basic
   interface implemented by the ideal functionality that is the
   corresponding argument to which id1 is applied in the "simulates"
   clause, and and b is that basic interface (possibly filtered to
   have only incoming or outgoing message) *)

type basic_inter_path = symbol list * basic_inter_body_tyd

(* three kinds of basic_inter_path's - ones of a direct interface,
   ones of an adversarial interface, and internal ones (coming from a
   real functionality's parameters' and subfunctionalities' direct
   interfaces) *)

type all_basic_inter_paths =
  {direct : basic_inter_path list; adversarial : basic_inter_path list;
   internal : basic_inter_path list}

let all_non_adv_basic_inter_paths (abip : all_basic_inter_paths)
      : all_basic_inter_paths =
  {direct = abip.direct; adversarial = []; internal = abip.internal}

let flatten_all_basic_inter_paths (abip : all_basic_inter_paths)
      : basic_inter_path list =
  abip.direct @ abip.adversarial @ abip.internal

let filter_dir_basic_inter_paths
    (dir : msg_dir) (bips : basic_inter_path list) : basic_inter_path list =
  List.map
  (fun (bip : basic_inter_path) ->
     (fst bip,
      IdMap.filter
      (fun _ (mbt : message_body_tyd) -> mbt.dir = dir)
      (snd bip)))
  bips

let incoming_abip (abip : all_basic_inter_paths) : all_basic_inter_paths =
  {direct      = filter_dir_basic_inter_paths In abip.direct;
   adversarial = filter_dir_basic_inter_paths In abip.adversarial;
   internal    = filter_dir_basic_inter_paths Out abip.internal}

let outgoing_abip (abip : all_basic_inter_paths) : all_basic_inter_paths =
  {direct      = filter_dir_basic_inter_paths Out abip.direct;
   adversarial = filter_dir_basic_inter_paths Out abip.adversarial;
   internal    = filter_dir_basic_inter_paths In abip.internal}

(* top can be the same as inter_id, but it can also be the name of
   a functionality parameter or subfunctionality *)

let get_basic_inter_paths
    (root : symbol) (top : symbol) (inter_id : symbol)
    (inter_map : inter_tyd IdPairMap.t) : basic_inter_path list =
  let getb_body (inter_id : symbol) : basic_inter_body_tyd =
    let inter = IdPairMap.find (root, inter_id) inter_map in
    match unloc inter with
    | BasicTyd b -> b
    | _          ->
        failure
        ("cannot happen, this function is called only on basic interfaces") in
  let inter = IdPairMap.find (root, inter_id) inter_map in
  match unloc inter with
  | BasicTyd b         -> [([top], b)]
  | CompositeTyd cimap ->
      IdMap.fold
      (fun subid inter_id l ->
         ([top; subid], getb_body inter_id) :: l)
      cimap []

let get_basic_inter_paths_from_inter_id
    (root : symbol) (inter_id : symbol) (inter_map : inter_tyd IdPairMap.t)
      : basic_inter_path list =
  get_basic_inter_paths root inter_id inter_id inter_map

let get_inter_id_paths_from_inter_id
    (root : symbol) (inter_id : symbol) (inter_map : inter_tyd IdPairMap.t)
      : symbol list list =
  List.map fst (get_basic_inter_paths_from_inter_id root inter_id inter_map)

let get_external_inter_id_paths
    (root : symbol) (id_dir_inter : symbol) (id_adv_inter : symbol option)
    (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t) : symbol list list =
  let dir = get_inter_id_paths_from_inter_id root id_dir_inter dir_inter_map in
  let adv =
    match id_adv_inter with
    | Some id -> get_inter_id_paths_from_inter_id root id adv_inter_map
    | None    -> [] in
  dir @ adv

let invert_basic_inter_path (bip : basic_inter_path) : basic_inter_path =
  let bibt = snd bip in
  let bibt_inv = invert_basic_inter_body_tyd bibt in
  (fst bip, bibt_inv)

let check_inter_id_paths_unique
    (msgf : formatter -> unit) (idps : symbol list located list) : unit =
  ignore
  (List.fold_left
   (fun l idp ->
      let uidp = unloc idp in
      if List.mem uidp l
      then error_message (loc idp) msgf
      else uidp :: l)
   [] idps)

let check_inter_id_path
    (root : symbol) (id_dir_inter : symbol) (id_adv_inter : symbol option)
    (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (iidp : symbol list located) : unit =
  let uidp = unloc iidp in
  let ps =
    get_external_inter_id_paths root id_dir_inter id_adv_inter
    dir_inter_map adv_inter_map in
  if  not (List.mem uidp ps)
  then error_message (loc iidp)
       (fun ppf ->
          fprintf ppf
          ("@[the@ party@ must@ serve@ sub-interfaces@ of@ the@ " ^^
           "composite@ interfaces@ implemented@ by@ the@ " ^^
           "functionality:@;<1 2>%a@]")
          format_id_paths_comma ps)

let check_served_inter_id_paths (serves : symbol list located list) : unit =
  let er ppf =
    fprintf ppf
    ("@[a@ party@ may@ serve@ at@ most@ one@ basic@ direct@ interface,@ " ^^
     "and@ at@ most@ one@ adversarial@ direct@ interface@]") in
  match List.length serves with
  | 0 -> ()
  | 1 -> ()
  | 2 ->
      if List.hd (unloc (List.nth serves 0)) <>
         List.hd (unloc (List.nth serves 1))
      then ()
      else error_message (mergelocs serves) er
  | _ -> error_message (mergelocs serves) er

let check_inter_id_paths_coverage
    (root : symbol) (id_dir_inter : symbol) (id_adv_inter : symbol option)
    (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (served_ps : symbol list located list) : unit =
  let serps = unlocs served_ps in
  let ps =
    get_external_inter_id_paths root id_dir_inter id_adv_inter
    dir_inter_map adv_inter_map in
  let unserved = List.filter (fun p -> not (List.mem p serps)) ps in
  if List.length unserved = 0
  then ()
  else error_message (mergelocs served_ps)
       (fun ppf ->
          fprintf ppf
          ("@[these@ sub-interfaces@ are@ not@ served@ by@ any@ " ^^
           "party:@;<1 2>%a@]")
          format_id_paths_comma unserved)

(* message paths and message path patterns *)

let string_of_msg_path (mp : msg_path) : string =
  let ump = unloc mp in
  let siop = string_of_id_path ump.inter_id_path in
  if siop = ""
  then ump.msg
  else siop ^ "." ^ ump.msg

let string_of_msg_path_pat (mpp : msg_path_pat) : string =
  let umpp = unloc mpp in
  let siop = string_of_id_path umpp.inter_id_path in
  let msg_or_star =
    match umpp.msg_or_star with
    | MsgOrStarMsg id -> id
    | MsgOrStarStar   -> "*" in
  if siop = "" then msg_or_star else siop ^ "." ^ msg_or_star

let format_msg_path_list
    (ppf : formatter) (mps : msg_path list) : unit =
  format_strings_comma ppf (List.map string_of_msg_path mps)

let msg_paths_of_basic_inter_path (bp : basic_inter_path) : msg_path list =
  IdMap.fold
  (fun id _ l ->
     dummyloc {inter_id_path = fst bp; msg = id} :: l)
  (snd bp) []

let msg_paths_of_basic_inter_paths
    (bpl : basic_inter_path list) : msg_path list =
  List.flatten (List.map (fun bp -> msg_paths_of_basic_inter_path bp) bpl)

let msg_paths_of_all_basic_inter_paths (abip : all_basic_inter_paths)
      : msg_path list =
  msg_paths_of_basic_inter_paths (flatten_all_basic_inter_paths abip)

let iidp1_starts_with_iidp2
    (iidp1 : string list) (iidp2 : string list) : bool =
      List.for_all
      identity
      (List.mapi
       (fun i id2 ->
          match List.nth_opt iidp1 i with
          | Some id1 -> id1 = id2
          | None     -> false)
       iidp2)

let check_outgoing_msg_path
    (abip : all_basic_inter_paths) (mp : msg_path) : unit =
  let allps = msg_paths_of_all_basic_inter_paths abip in
  if List.exists
     (fun p -> string_of_msg_path p = string_of_msg_path mp)
     allps
  then ()
  else error_message (loc mp)
       (fun ppf ->
          fprintf ppf
          ("@[message@ path@ is@ not@ one@ of@ the@ possible@ outgoing@ " ^^
           "message@ paths:@;<1 2>%a@]")
       format_msg_path_list allps)

let check_msg_path_pat
    (abip : all_basic_inter_paths) (sc : state_context)
    (mpp : msg_path_pat) : unit =
  let init_and_sim = sc.initial && sc.kind = SimKind in
  let init_and_non_sim = sc.initial && not (sc.kind = SimKind) in
  let allmps = msg_paths_of_all_basic_inter_paths abip in
  let restrmps =
    if init_and_sim
      then List.filter
           (fun mps -> List.length (unloc mps).inter_id_path = 1)
           allmps
    else if init_and_non_sim
      then msg_paths_of_all_basic_inter_paths
           (all_non_adv_basic_inter_paths abip)
    else allmps in
  let () =
    if List.is_empty restrmps
    then error_message (loc mpp)
         (fun ppf ->
            fprintf ppf
            "@[no@ incoming@ message@ paths@ in@ this@ state@]") in
  match (unloc mpp).msg_or_star with
  | MsgOrStarMsg _  ->
      if List.exists
         (fun mp -> string_of_msg_path mp = string_of_msg_path_pat mpp)
         restrmps
        then ()
      else if List.exists  (* is initial state *)
              (fun mp -> string_of_msg_path mp = string_of_msg_path_pat mpp)
              allmps
        then error_message (loc mpp)
             (fun ppf ->
                fprintf ppf
                ("@[message@ path@ is@ not@ one@ of@ the@ possible@ " ^^
                 "incoming@ message@ paths@ for@ initial@ state:@;<1 2>%a@]")
                format_msg_path_list restrmps)
      else error_message (loc mpp)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ is@ not@ one@ of@ the@ possible@ " ^^
               "incoming@ message@ paths:@;<1 2>%a@]")
              format_msg_path_list restrmps)
  | MsgOrStarStar   ->
      if (List.exists
          (fun mp ->
             iidp1_starts_with_iidp2 (unloc mp).inter_id_path
             (unloc mpp).inter_id_path)
          restrmps)
        then ()
      else if (List.exists  (* is initial state *)
              (fun mp ->
                 iidp1_starts_with_iidp2
                 (unloc mp).inter_id_path (unloc mpp).inter_id_path)
              allmps)
        then error_message (loc mpp)
             (fun ppf ->
                fprintf ppf
                ("@[message@ path@ pattern@ is@ inconsistent@ with@ the@ " ^^
                 "paths@ of@ possible@ incoming@ messages@ for@ initial@ " ^^
                 "state:@;<1 2>%a@]")
                 format_msg_path_list restrmps)
      else error_message (loc mpp)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ pattern@ is@ inconsistent@ with@ the@ " ^^
               "paths@ of@ possible@ incoming@ messages:@;<1 2>%a@]")
               format_msg_path_list restrmps)

let remove_covered_paths
    (mps : msg_path list) (mpp : msg_path_pat) (is_init : bool)
      : msg_path list =
  let covered mp1 mpp2 =
    match (unloc mpp2).msg_or_star with
    | MsgOrStarMsg _  ->
        string_of_msg_path mp1 = string_of_msg_path_pat mpp2
    | MsgOrStarStar   ->
        iidp1_starts_with_iidp2
        (unloc mp1).inter_id_path (unloc mpp2).inter_id_path in
  let rem = List.filter (fun mp' -> not (covered mp' mpp)) mps in
  if List.length mps = List.length rem
  then if is_init
       then error_message (loc mpp)
            (fun ppf ->
               fprintf ppf
               ("@[this@ pattern@ is@ covered@ by@ previous@ patterns@ and@ " ^^
                "would@ never@ match,@ in@ initial@ state@]"))
       else error_message (loc mpp)
            (fun ppf ->
               fprintf ppf
               ("@[this@ pattern@ is@ covered@ by@ previous@ patterns@ and@ " ^^
                "would@ never@ match@]"))
  else rem

let coverage_msg_path_pats
    (abip : all_basic_inter_paths) (sc : state_context)
    (mpps : msg_path_pat list) : msg_path list =
  let allmps = msg_paths_of_all_basic_inter_paths abip in
  let restrmps =
    if sc.initial && sc.kind = SimKind
      then List.filter
           (fun mps -> List.length (unloc mps).inter_id_path = 1)
           allmps
    else if sc.initial && sc.kind <> SimKind
      then msg_paths_of_all_basic_inter_paths
           (all_non_adv_basic_inter_paths abip)
    else allmps in
  List.fold_left
  (fun mps mp -> remove_covered_paths mps mp sc.initial)
  restrmps mpps

let check_coverage_msg_path_pats
    (abip : all_basic_inter_paths) (sc : state_context)
    (mml : (EcIdent.t * ty) msg_pat list) : unit =
  let abip = incoming_abip abip in
  let r =
    coverage_msg_path_pats abip sc
    (List.map (fun (mm : (EcIdent.t * ty) msg_pat) -> mm.msg_path_pat) mml) in
  if r <> []
  then let l = loc (List.last mml).msg_path_pat in
       error_message l
       (fun ppf ->
          fprintf ppf
          ("@[message@ patterns@ are@ not@ exhaustive;@ these@ " ^^
           "messages@ are@ not@ matched:@;<1 2>%a@]")
          format_msg_path_list r)

(* pattern matching *)

let check_port_id_binding
    (abip : all_basic_inter_paths) (idp : symbol list)
    (id : psymbol) (sc : state_context) (env : env) : EcIdent.t located * env =
  let l = loc id in
  let d = List.exists (fun bp -> fst bp = idp) abip.direct in
  let is_sim = sc.kind = SimKind in
  if not d
  then error_message l
       (fun ppf ->
          fprintf ppf
          (if is_sim
           then ("@[message@ patterns@ matching@ adversarial@ messages@ " ^^
                 "may@ not@ bind@ source@ ports@ to@ identifiers")
           else ("@[message@ patterns@ matching@ adversarial@ and@ " ^^
                 "internal@ messages@ may@ not@ bind@ source@ ports@ " ^^
                 "to@ identifiers@]")))
  else let id' = EcIdent.create (unloc id) in
       (mk_loc l id', bind_local_avoid_var env sc id' port_ty l)

let check_non_port_id_binding
    (abip : all_basic_inter_paths) (idp : symbol list) (mppl : EcLocation.t)
      : unit =
  let d = List.exists (fun bp -> fst bp = idp) abip.direct in
  if d
  then error_message mppl
       (fun ppf ->
          fprintf ppf
          ("@[non-\"*\"@ message@ patterns@ matching@ messages@ of@ direct@ " ^^
           "interfaces@ implemented@ by@ functionalities@ must@ bind@ " ^^
           "source@ ports@ to@ identifiers@]"))
  else ()

let check_pat_add_id
    (sc : state_context) (env : env) (pat : symbol pat) (ty : ty)
      : (EcIdent.t * ty) pat * env =
  match pat with
  | PatWildcard l -> (PatWildcard l, env)
  | PatId id      ->
      let l = loc id in
      let id' = EcIdent.create (unloc id) in
      (PatId (mk_loc l (id', ty)), bind_local_avoid_var env sc id' ty l)

let ids_of_pat (pat : symbol pat) : IdSet.t =
  match pat with
  | PatWildcard _ -> IdSet.empty
  | PatId id      -> IdSet.singleton (unloc id)

let ids_of_pats (pats : symbol pat list) : IdSet.t =
  List.fold_left
  (fun uids pat -> IdSet.union uids (ids_of_pat pat))
  IdSet.empty pats

let check_disjoint_bindings (pats : symbol pat list) : unit =
  ignore
  (List.fold_left
   (fun uids pat ->
      let pat_uids = ids_of_pat pat in
      let com_uids = IdSet.inter uids pat_uids in
      if IdSet.is_empty com_uids
      then IdSet.union uids pat_uids
      else let ex_com = IdSet.choose com_uids in
           error_message (get_loc_pat_list pats)
           (fun ppf ->
              fprintf ppf "@[pattern@ binds@ %s@ more@ than@ once@]" ex_com))
   IdSet.empty pats)

let check_pat_args_with_msg_type
    (bips : basic_inter_path list) (mp : symbol list * symbol)
    (pats : symbol pat list) (env : env) (sc : state_context)
      : (EcIdent.t * ty) pat list * env =
  let bip = List.find (fun p -> fst p = fst mp) bips in
  let mtyp =
    indexed_map_to_list
    (unlocm (IdMap.find (snd mp) (snd bip)).params_map) in
  let () =
    if List.length mtyp <> List.length pats
    then error_message (get_loc_pat_list pats)
         (fun ppf ->
            fprintf ppf
            ("@[the@ number@ of@ argument@ patterns@ is@ different@ " ^^
             "from@ the@ number@ of@ message@ parameters@]")) in
  let () = check_disjoint_bindings pats in
  List.fold_left2
  (fun (pats, env) pat ty ->
     let (pat, env) = (check_pat_add_id sc env pat ty) in
     (pats @ [pat], env))
  ([], env) pats mtyp

let check_missing_pat_args_with_msg_type
    (bips : basic_inter_path list) (mp : symbol list * symbol)
    (l : EcLocation.t) : unit =
  let bip = List.find (fun p -> fst p = fst mp) bips in
  if not (IdMap.is_empty ((IdMap.find (snd mp) (snd bip)).params_map))
  then error_message l
         (fun ppf ->
            fprintf ppf
            ("@[the@ number@ of@ argument@ patterns@ is@ different@ " ^^
             "from@ the@ number@ of@ message@ parameters@]"))

let check_pat_args
    (bips : basic_inter_path list) (msg_pat : symbol msg_pat) (env : env)
    (sc : state_context) : (EcIdent.t * ty) pat list option * env =
  match msg_pat.pat_args with
  | None      ->
      let () =
        let mpp = msg_pat.msg_path_pat in
        let l = loc mpp in
        let mpp_u = unloc mpp in
        match mpp_u.msg_or_star with
        | MsgOrStarStar   -> ()
        | MsgOrStarMsg id ->
            check_missing_pat_args_with_msg_type bips
            (mpp_u.inter_id_path, id) l in
      (None, env)
  | Some pats ->
      let mpp = msg_pat.msg_path_pat in
      let mpp_u = unloc mpp in
       match mpp_u.msg_or_star with
       | MsgOrStarStar   -> failure "cannot happen - check in parser"
       | MsgOrStarMsg id ->
           let (pats, env) =
             check_pat_args_with_msg_type bips
             (mpp_u.inter_id_path, id) pats env sc
           in (Some pats, env)

let check_msg_pat
    (abip : all_basic_inter_paths) (msg_pat : symbol msg_pat)
    (sc : state_context) (env : env) : (EcIdent.t * ty) msg_pat * env =
  let abip = incoming_abip abip in
  let () = check_msg_path_pat abip sc msg_pat.msg_path_pat in
  let (port_id, env) =
    match msg_pat.port_id with
    | Some id ->
        (* we know msg_pat.msg_path_pat does not end in "*" *)
        let () =
          let uids_pat_args = ids_of_pats (msg_pat.pat_args |? []) in
          if IdSet.mem (unloc id) uids_pat_args
          then error_message (loc id)
               (fun ppf ->
                  fprintf ppf
                  ("@[source@ port@ of@ message@ pattern@ is@ also@ bound@ " ^^
                   "in@ message@ argument@ patterns@]")) in
        let (id, env) =
          check_port_id_binding abip
          ((unloc msg_pat.msg_path_pat).inter_id_path) id sc env
        in Some id, env
    | None    ->
        if msg_path_pat_ends_star msg_pat.msg_path_pat
        then (None, env)
        else let mppl = loc msg_pat.msg_path_pat in
             (check_non_port_id_binding abip
              ((unloc msg_pat.msg_path_pat).inter_id_path) mppl;
              (None, env)) in
  let bips = flatten_all_basic_inter_paths abip in
  let (pat_args, env) = check_pat_args bips msg_pat env sc in
  let port_id =
    EcUtils.omap
    (fun id -> mk_loc (loc id) (unloc id, port_ty))
    port_id in
  ({port_id      = port_id;
    msg_path_pat = msg_pat.msg_path_pat;
    pat_args     = pat_args},
   env)

(* checking instructions *)

let check_uninitialized_var (exp : form) (l : EcLocation.t)
    (sa : state_analysis) : unit =
  let fv = f_fv exp in
  EcIdent.Mid.iter
  (fun ident _ ->
     let id = EcIdent.name ident in
     if IdSet.mem id sa.uninit_vs
     then error_message l
          (fun ppf ->
             Format.fprintf ppf
             "@[expression@ uses@ possibly@ uninitialzed@ variable:@ %s@]"
             id))
  fv

(* if expct_ty_opt is Some ty, then ty must not have any unification
   variables *)

let check_expr
    (sa : state_analysis) (env : env) (ue : unienv)
    (pform : pformula) (expct_ty_opt : ty option) : form * ty =
  let form = trans_form_opt env ue pform None in
  let ty = form.f_ty in
  let () =
    match expct_ty_opt with
    | None          -> ()
    | Some expct_ty ->
        unify_or_fail env ue (loc pform) ~expct:expct_ty ty in
  (* check for possibly uninitialized variables *)
  let () = check_uninitialized_var form (loc pform) sa in
  (form, ty)

let check_lhs_var (sc : state_context) (sa : state_analysis) (id : psymbol)
      : state_analysis * ty =
  match IdMap.find_opt (unloc id) sc.vars with
  | None   ->
      error_message (loc id)
      (fun ppf ->
         fprintf ppf
         "@[identifer@ is@ not@ a@ local@ variable@]")
  | Some u -> (refine_state_analysis sa (unloc id), snd (unloc u))

let check_lhs (sc : state_context) (sa : state_analysis) (lhs : lhs) =
  match lhs with
  | LHSSimp id   -> check_lhs_var sc sa id
  | LHSTuple ids ->
      let () =
        match find_dup
              ~cmp:(fun id1 id2 -> compare (unloc id1) (unloc id2))
              ids with
        | None    -> ()
        | Some id ->
            error_message (loc id)
            (fun ppf ->
               Format.fprintf ppf
               ("@[duplicate@ identifer@ in@ left-hand-side@ of@ " ^^
                "assignment@]")) in
      let (sa, tys) =
        List.fold_left
        (fun p id ->
           let (sa, ty) = check_lhs_var sc (fst p) id in
           (sa, snd p @ [ty]))
        (sa, []) ids in
      (sa, ttuple tys)

let check_val_assign
    (sc : state_context) (sa : state_analysis) (env : env) (ue : unienv)
    (lhs : lhs) (ex : pformula)
      : instruction_tyd_u * state_analysis =
  let (sa', ty) = check_lhs sc sa lhs in
  let (exp, _) = check_expr sa env ue ex (Some ty) in
  Assign (lhs, exp), sa'

let check_sampl_assign
    (sc : state_context) (sa : state_analysis) (env : env) (ue : unienv)
    (lhs : lhs) (ex : pformula)
      : instruction_tyd_u * state_analysis =
  let (sa', ty) = check_lhs sc sa lhs in
  let (exp, _) = check_expr sa env ue ex (Some (tdistr ty)) in
  Sample (lhs, exp), sa'

let check_state_expr
    (ss : state_sig IdMap.t) (sc : state_context) (sa : state_analysis)
    (env : env) (ue : unienv) (se : state_expr) : state_expr_tyd =
  let (is_init, tys) =
    try IdMap.find (unloc se.id) ss with
    | Not_found ->
        error_message (loc se.id)
        (fun ppf ->
           fprintf ppf "@[non-existing@ state:@ %s@]" (unloc se.id)) in
  let () =
    if is_init
    then if is_real_kind sc.kind
           then error_message (loc se.id)
                (fun ppf ->
                   fprintf ppf
                   ("@[party@ of@ real@ functionality@ cannot@ transition@ " ^^
                    "back@ to@ initial@ state@]"))
         else if is_ideal_kind sc.kind || is_ideal_no_adv_kind sc.kind
           then error_message (loc se.id)
                (fun ppf ->
                   fprintf ppf
                   ("@[ideal functionality@ cannot@ transition@ back@ " ^^
                    "to@ initial@ state@]"))
         else error_message (loc se.id)  (* simulator *)
              (fun ppf ->
                 fprintf ppf
                 ("@[simulator@ cannot@ transition@ back@ " ^^
                  "to@ initial@ state@]")) in
  let args = se.args in
  if List.length tys <> List.length (unloc args)
  then error_message (loc args)
       (fun ppf -> fprintf ppf "@[wrong@ number@ of@ state@ arguments@]")
  else
    let argz_u = List.map2
       (fun sigt sip -> fst (check_expr sa env ue sip (Some sigt)))
       tys (unloc args) in
    let argz = mk_loc (loc args) argz_u in
    {id = se.id; args = argz}

let check_msg_arguments
    (sa : state_analysis) (env : env) (ue : unienv)
    (es : pformula list located) (mc : ty_index IdMap.t)
      : form list located =
  let sg = indexed_map_to_list (unlocm mc) in
  if List.length (unloc es) <> List.length sg
  then error_message (loc es)
       (fun ppf ->
          fprintf ppf "@[wrong@ number@ of@ message@ arguments@]")
  else
    let exps = List.map2
       (fun ex typ -> fst (check_expr sa env ue ex (Some typ)))
       (unloc es) sg in
    mk_loc (loc es) exps

let check_send_direct
    (sa : state_analysis) (env : env) (ue : unienv)
    (msg : msg_expr) (param_tis : ty_index IdMap.t) : msg_expr_tyd =
  let l = loc msg.path in
  let port_exp =
    match msg.port_expr with
    | Some port_exp ->
        Some (fst (check_expr sa env ue port_exp (Some port_ty)))
    | None          ->
        error_message l
        (fun ppf ->
           fprintf ppf
           ("@[outgoing@ messages@ to@ sub-interfaces@ of@ composite@ " ^^
            "direct@ interfaces@ must@ have@ destination@ ports@]")) in
  let args = check_msg_arguments sa env ue msg.args param_tis in
  {path = msg.path; args = args; port_expr = port_exp}

let check_send_adversarial
    (sa : state_analysis) (env : env) (ue : unienv)
    (msg : msg_expr) (param_tis : ty_index IdMap.t) : msg_expr_tyd =
  let () =
    match msg.port_expr with
    | Some port_exp ->
        error_message (loc port_exp)
        (fun ppf ->
           fprintf ppf
           "@[adversarial@ messages@ must@ not@ have@ destination@ ports@]")
    | None          -> () in
  let args = check_msg_arguments sa env ue msg.args param_tis in
  {path = msg.path; args = args; port_expr = None}

let check_send_internal
    (sa : state_analysis) (env : env) (ue : unienv)
    (msg : msg_expr) (param_tis : ty_index IdMap.t) : msg_expr_tyd =
  let () =
    match msg.port_expr with
    | Some port_exp ->
        error_message (loc port_exp)
        (fun ppf ->
           fprintf ppf
           ("@[messages@ to@ subfunctionalities@ must@ not@ have@ " ^^
            "destination@ ports@]"))
    | None          -> () in
  let args = check_msg_arguments sa env ue msg.args param_tis in
  {path = msg.path; args = args; port_expr = None}

let is_msg_path_in_basic_inter_paths
    (mp : msg_path) (bips : basic_inter_path list) : bool =
  let bipo =
    List.find_opt (fun bip -> fst bip = (unloc mp).inter_id_path) bips in
  Option.is_some bipo

let get_msg_def_for_msg_path
    (mp : msg_path) (bips : basic_inter_path list) : message_body_tyd =
  let iip = (unloc mp).inter_id_path in
  let msg = (unloc mp).msg in
  let bip = List.find (fun bip -> fst bip = iip) bips in
  IdMap.find msg (snd bip)

let check_send_msg_path
    (msg : msg_expr) (abip : all_basic_inter_paths) : unit =
  let abip = outgoing_abip abip in
  check_outgoing_msg_path abip msg.path

let check_msg_expr
    (abip : all_basic_inter_paths) (sc : state_context) (sa : state_analysis)
    (env : env) (ue : unienv) (msg : msg_expr) : msg_expr_tyd =
  let () = check_send_msg_path msg abip in
  let bips = abip.direct @ abip.adversarial @ abip.internal in
  let param_tis = (get_msg_def_for_msg_path msg.path bips).params_map in
  let l = loc msg.path in
  match sc.kind with
  | RealPartyKind serves_basic_adv ->
      if is_msg_path_in_basic_inter_paths msg.path abip.adversarial
        then check_send_adversarial sa env ue msg param_tis
      else if sc.initial && serves_basic_adv
        then error_message l
             (fun ppf ->
                fprintf ppf
                ("@[send@ and@ transition@ of@ initial@ state@ "   ^^
                 "of@ party@ of@ real@ functionality@ that@ "      ^^
                 "serves@ basic@ adversarial@ interface@ "         ^^
                 "must@ send@ adversarial@ message@ to@ adversary"))
      else if is_msg_path_in_basic_inter_paths msg.path abip.direct
        then check_send_direct sa env ue msg param_tis
      else if is_msg_path_in_basic_inter_paths msg.path abip.internal
        then check_send_internal sa env ue msg param_tis
      else failure "impossible - will be one of above"
  | IdealKind                      ->
      if sc.initial
      then if is_msg_path_in_basic_inter_paths msg.path abip.direct
             then error_message l
                  (fun ppf ->
                     fprintf ppf
                     ("@[send@ and@ transition@ of@ initial@ state@ "    ^^
                      "of@ ideal@ functionality@ with@ adversarial@ "    ^^
                      "interface@ must@ send@ adversarial@ message@ "    ^^
                      "(to@ simulator@ if@ there@ is@ one,@ otherwise@ " ^^
                      "to@ adversary)@]"))
           else if is_msg_path_in_basic_inter_paths msg.path abip.adversarial
             then check_send_adversarial sa env ue msg param_tis
           else failure "impossible - will be one of above"
      else if is_msg_path_in_basic_inter_paths msg.path abip.direct
             then check_send_direct sa env ue msg param_tis
           else if is_msg_path_in_basic_inter_paths msg.path abip.adversarial
             then check_send_adversarial sa env ue msg param_tis
           else failure "impossible - will be one of above"
  | IdealNoAdvKind                 ->
      if is_msg_path_in_basic_inter_paths msg.path abip.direct
        then check_send_direct sa env ue msg param_tis
      else if is_msg_path_in_basic_inter_paths msg.path abip.adversarial
        then check_send_adversarial sa env ue msg param_tis
      else failure "impossible - will be one of above"
  | SimKind                        ->
      if is_msg_path_in_basic_inter_paths msg.path abip.adversarial
      then check_send_adversarial sa env ue msg param_tis
      else failure "impossible - will be above"

let check_send_and_transition
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env) (ue : unienv)
    (sat : send_and_transition) : instruction_tyd_u =
  let msg_exp = check_msg_expr abip sc sa env ue sat.msg_expr in
  let state_exp = check_state_expr ss sc sa env ue sat.state_expr in
  SendAndTransition {msg_expr = msg_exp; state_expr = state_exp}

let check_toplevel_match_clause
    (l : EcLocation.t) (env : env) (ue : unienv) (gindty : ty)
    (clause : match_clause) : symbol * (bindings * instruction list located) =
  let filter = fun _ op -> EcDecl.is_ctor op in
  let PPApp ((cname, tvi), cargs) = fst clause in
  let tvi = tvi |> EcUtils.omap (transtvi env ue) in
  let cts = EcUnify.select_op ~filter tvi env (unloc cname) ue ([], None) in
  match cts with
  | []                          ->
      tyerror cname.pl_loc env (InvalidMatch FXE_CtorUnk)
  | _ :: _ :: _                 ->
      tyerror cname.pl_loc env (InvalidMatch FXE_CtorAmbiguous)
  | [(cp, tvi), opty, subue, _] ->
      let ctor = EcUtils.oget (EcEnv.Op.by_path_opt cp env) in
      let (indp, ctoridx) = EcDecl.operator_as_ctor ctor in
      let indty = EcUtils.oget (EcEnv.Ty.by_path_opt indp env) in
      let ind = (EcUtils.oget (EcDecl.tydecl_as_datatype indty)).tydt_ctors in
      let ctorsym, ctorty = List.nth ind ctoridx in
      let args_exp = List.length ctorty in
      let args_got = List.length cargs in

      if args_exp <> args_got
      then tyerror cname.pl_loc env
           (InvalidMatch
            (FXE_CtorInvalidArity (snd (unloc cname), args_exp, args_got)));

      let cargs_lin =
        List.filter_map (fun o -> EcUtils.omap unloc (unloc o)) cargs in
      if has_dup cargs_lin
      then tyerror cname.pl_loc env (InvalidMatch FXE_MatchNonLinear);

      EcUnify.UniEnv.restore ~src:subue ~dst:ue;

      let ctorty =
        let tvi = Some (EcUnify.TVIunamed tvi) in
          fst (EcUnify.UniEnv.opentys ue indty.tyd_params tvi ctorty) in
      let pty = EcUnify.UniEnv.fresh ue in

      (try EcUnify.unify env ue (toarrow ctorty pty) opty with
       | EcUnify.UnificationFailure _ -> assert false);
      unify_or_fail env ue l ~expct:pty gindty;
      let create o = EcIdent.create (EcUtils.omap_dfl unloc "_" o) in
      let pvars =
        List.map
        (fun x -> mk_loc (loc x) (create (unloc x)))
        cargs in
      let pvars = List.combine pvars ctorty in

      ctorsym, (pvars, snd clause)

let rec check_ite
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env) (ue : unienv)
    (ex : pformula) (tins : instruction list located)
    (eins_opt : instruction list located option)
    : instruction_tyd_u * state_analysis =
  let ex, _ = check_expr sa env ue ex (Some tbool) in
  let sa1 = check_instructions abip ss sc sa env ue tins in
  let sa2 =
    match eins_opt with
    | None      -> (None, sa)
    | Some eins ->
        (let (ins, sa) =
           check_instructions abip ss sc sa env ue eins in
         (Some ins, sa)) in
  ITE (ex, fst sa1, fst sa2),
  merge_state_analysis (snd sa1) (snd sa2)

and check_match
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env) (ue : unienv)
    (ex : pformula) (clauses : match_clause list located)
      : instruction_tyd_u * state_analysis =
  let ex_loc = loc ex in
  let exp, ty = check_expr sa env ue ex None in
  let uidmap = EcUnify.UniEnv.assubst ue in
  let ty = EcFol.ty_subst (EcFol.Tuni.subst uidmap) ty in
  let inddecl =
    match (EcEnv.ty_hnorm ty env).ty_node with
    | Tconstr (indp, _) -> begin
        match EcEnv.Ty.by_path indp env with
        | { tyd_type = `Datatype dt } -> Some (indp, dt)
        | _                           -> None
      end
    | _                 -> None in
  let (_, inddecl) =
    match inddecl with
    | None   -> tyerror ex.pl_loc env NotAnInductive
    | Some x -> x in
  let top_results =
    List.map
    (check_toplevel_match_clause ex_loc env ue ty)
    (unloc clauses) in
  (* the left-hand-sides of top_results are a subset of the left-hand sides
     of inddecl.tydt_ctors (with the order perhaps different) *)
  let () =
    if List.length top_results < List.length inddecl.tydt_ctors
      then tyerror (loc clauses) env (InvalidMatch FXE_MatchPartial)
    else if has_dup ~cmp:(fun x y -> compare (fst x) (fst y))
            top_results
      then tyerror (loc clauses) env (InvalidMatch FXE_MatchDupBranches) in
  (* the left-hand-sides of top_results are exactly the left-hand sides
     of inddecl.tydt_ctors (with the order perhaps different) *)
  let results =
    List.map
    (fun (cons, (bndgs, body)) ->
       let env = bind_locals_avoid_var env sc bndgs in
       cons, (bndgs, check_instructions abip ss sc sa env ue body))
    top_results in
  let cls_u =
    List.map
    (fun (cons, (bndngs, (ins, _))) ->
       cons, (bndngs, ins))
    results in
  let cls = mk_loc (loc clauses) cls_u in
  let sas = List.map (fun (_, (_, (_, sa))) -> sa) results in
  Match(exp, cls), merge_state_analyses sas

and check_instruction
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (env : env) (ue : unienv)
    (sa : state_analysis) (i : instruction)
      : instruction_tyd * state_analysis =
  let uinstr, sa =
    match unloc i with
    | Assign (lhs, ex)                    ->
        check_val_assign sc sa env ue lhs ex
    | Sample (lhs, ex)                    ->
        check_sampl_assign sc sa env ue lhs ex
    | ITE (ex, tins, eins)                ->
        check_ite abip ss sc sa env ue ex tins eins
    | Match(ex, clauses)                  ->
        check_match abip ss sc sa env ue ex clauses
    | SendAndTransition sat               ->
        check_send_and_transition abip ss sc sa env ue sat, sa
    | Fail                                -> Fail, sa in
  (mk_loc (loc i) uinstr), sa

and check_instructions
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env) (ue : unienv)
    (is : instruction list located)
      : instruction_tyd list located * state_analysis =
  let uis = unloc is in
  let uis', sa' =
    List.fold_left
    (fun (il,sa) i ->
       let i', sa' = check_instruction abip ss sc env ue sa i in
       ((il @ [i']), sa') ) ([], sa) uis in
  (mk_loc (loc is) uis'), sa'

(* checking where control transfer instructions (send-and-transition and
   fail) may appear *)

let illegal_control_transfer (l : EcLocation.t) =
  error_message l
  (fun ppf ->
     fprintf ppf
     ("@[control@ transfer@ by@ \"fail\"@ or@ \"send-and-transition\"@ " ^^
      "instruction@ is@ only@ allowed@ at@ end@ of@ message@ match@ clause@]"))

let failure_to_transfer_control (l : EcLocation.t) =
  error_message l
  (fun ppf ->
     fprintf ppf
     ("@[message@ match@ clause@ must@ end@ with@ control@ transfer@ via@ " ^^
      "\"fail\"@ or@ \"send-and-transition\"@ instruction@]"))

let rec check_instrs_transfer_at_end (is : instruction_tyd list located)
          : unit =
  let uis = unloc is in
  match uis with
  | [] -> failure_to_transfer_control (loc is)
  | is ->
      let xs = List.take (List.length is - 1) is in
      (List.iter check_instr_not_transfer xs;
       check_instr_end_in_transfer (List.last is))

and check_instrs_not_transfer (is : instruction_tyd list located) : unit =
  let uis = unloc is in
  List.iter check_instr_not_transfer uis

and check_instr_end_in_transfer (instr : instruction_tyd) : unit =
  let uinstr = unloc instr in
  match uinstr with
  | Assign _                    -> failure_to_transfer_control (loc instr)
  | Sample _                    -> failure_to_transfer_control (loc instr)
  | ITE (_, thens, elses)       ->
      (check_instrs_transfer_at_end thens;
       match elses with
       | None       -> failure_to_transfer_control (loc instr)
       | Some elses -> check_instrs_transfer_at_end elses)
  | Match (_, clauses)          ->
      List.iter
      (fun (_, (_, is)) -> check_instrs_transfer_at_end is)
      (unloc clauses)
  | SendAndTransition _         -> ()
  | Fail                        -> ()

and check_instr_not_transfer (instr : instruction_tyd) : unit =
  let uinstr = unloc instr in
  match uinstr with
  | Assign _                    -> ()
  | Sample _                    -> ()
  | ITE (_, thens, elses)       ->
      (check_instrs_not_transfer thens;
       match elses with
       | None       -> ()
       | Some elses -> check_instrs_not_transfer elses)
  | Match (_, clauses)          ->
      List.iter
      (fun (_, (_,is)) -> check_instrs_not_transfer is)
      (unloc clauses)
  | SendAndTransition _         -> illegal_control_transfer (loc instr)
  | Fail                        -> illegal_control_transfer (loc instr)

(* checking message match clauses *)

let replace_unif_vars_in_msg_match_code (ue : unienv)
    (is : instruction_tyd list located) : instruction_tyd list located =
  let uidmap =
    try EcUnify.UniEnv.close ue with
    | EcUnify.UninstanciateUni ->
        error_message (loc is)
        (fun ppf ->
           Format.fprintf ppf
           "@[message@ match@ clause@ body@ must@ be@ monomorphic@]") in
  let ts = EcFol.Tuni.subst uidmap in
  let subst_ty = EcFol.ty_subst ts in
  let subst_form = EcFol.Fsubst.f_subst ts in
  let replace_expr_list_loc exps =
    mk_loc (loc exps) (List.map subst_form (unloc exps)) in
  let replace_expr_opt = EcUtils.omap subst_form in
  let replace_sat sat =
    let {msg_expr; state_expr} = sat in
    {msg_expr =
       {path      = msg_expr.path;
        args      = replace_expr_list_loc msg_expr.args;
        port_expr = replace_expr_opt msg_expr.port_expr};
     state_expr =
       {id   = state_expr.id;
        args = replace_expr_list_loc state_expr.args}} in

  let rec replace ins =
    mk_loc (loc ins)
    (match unloc ins with
     | Assign (lhs, exp)       -> Assign (lhs, subst_form exp)
     | Sample (lhs, exp)       -> Sample (lhs, subst_form exp)
     | ITE (exp, thens, elses) ->
         ITE
         (subst_form exp,
          mk_loc (loc thens) (List.map replace (unloc thens)),
          EcUtils.omap
          (fun is -> mk_loc (loc is) (List.map replace (unloc is)))
          elses)
     | Match (exp, clauses)    ->
         Match (subst_form exp, replace_match_clauses clauses)
     | SendAndTransition sat   -> SendAndTransition (replace_sat sat)
     | Fail                    -> Fail)
  and replace_match_clauses clauses =
    mk_loc (loc clauses)
    (List.map
     (fun (cons, (bndgs, ins)) ->
        (cons,
         (List.map
          (fun (id, ty) -> (id, subst_ty ty))
          bndgs,
         mk_loc (loc ins) (List.map replace (unloc ins)))))
     (unloc clauses)) in
   mk_loc (loc is) (List.map replace (unloc is))

let check_msg_match_code
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env)
    (is : instruction list located) : instruction_tyd list located =
  let ue = unif_env () in
  let is = fst (check_instructions abip ss sc sa env ue is) in
  let is = replace_unif_vars_in_msg_match_code ue is in
  check_instrs_transfer_at_end is;
  is

let check_msg_match_clause
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env)
    (mmc : msg_match_clause) : msg_match_clause_tyd =
  let (msg_pat, env) = check_msg_pat abip mmc.msg_pat sc env in
  let code = check_msg_match_code abip ss sc sa env mmc.code in
  {msg_pat = msg_pat; code = code}

(* checking states *)

let check_state_code
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (env : env)
    (mmclauses : msg_match_clause list)
      : msg_match_clause_tyd list =
  let mmclauses' =
    List.map
    (fun mmc -> check_msg_match_clause abip ss sc sa env mmc)
    mmclauses in
  check_coverage_msg_path_pats abip sc
  (List.map (fun mmc -> mmc.msg_pat) mmclauses');
  mmclauses'

let check_exactly_one_initial_state
    (id : psymbol) (sds : state_def list) : psymbol =
  let inits =
    List.filter
    (fun sd ->
       match sd with
       | InitialState _ -> true
       | _              -> false)
    sds in
  match List.length inits with
  | 0 ->
      error_message (loc id)
      (fun ppf ->
         fprintf ppf "@[%s@ doesn't@ have@ initial@ state@]" (unloc id))
  | 1 ->
      (match List.hd inits with
       | InitialState s   -> s.id
       | FollowingState _ ->
           failure "impossible, list contains only InitialState")
  | _ ->
      error_message (loc id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ has@ more@ than@ one@ initial@ state@]" (unloc id))

(* check the top-level of a state_def *)

let check_toplevel_state (init_id : psymbol) (st : state) : state_mid =
  let is_initial = (init_id = st.id) in
  let params =
    check_name_type_bindings_top
    (fun ppf -> fprintf ppf "@[duplicate@ parameter@ name@]")
    (unloc st.params) in
  let vars =
    IdMap.map
    (fun ti -> mk_loc (loc ti) (fst (unloc ti)))
    (check_name_type_bindings_top
     (fun ppf -> fprintf ppf "@[duplicate@ variable@ name@]")
     st.code.vars) in
  let () =
    let dup =
      IdMap.find_first_opt (fun var -> IdMap.mem var params) vars in
    match dup with
    | None            -> ()
    | Some (var, typ) ->
        error_message (loc typ)
        (fun ppf ->
           fprintf ppf
           ("@[variable@ name@ %s@ is@ the@ same@ as@ one@ of@ the@ " ^^
            "state's@ parameters@]")
           var) in
  mk_loc (loc st.id)
  {is_initial = is_initial; params = params; vars = vars;
   mmclauses = st.code.mmclauses}

let drop_state_construct (sd : state_def) : state =
  match sd with
  | InitialState s   -> s
  | FollowingState s -> s

(* check the top-level of a state machine

   id is name of party (in case of real functionality), ideal
   functionality, or simulator - only used for error messages *)

let check_toplevel_states (id : psymbol) (state_defs : state_def list)
      : state_mid IdMap.t =
  let init_id = check_exactly_one_initial_state id state_defs in
  let states = List.map (fun sd -> drop_state_construct sd) state_defs in
  let state_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ state@ name@]")
    states (fun s -> s.id) in
  IdMap.map (check_toplevel_state init_id) state_map

(* check the lower-level of an individual state_tyd *)

let check_lowlevel_state
    (abip : all_basic_inter_paths) (kind : kind)
    (internal_ports : QidSet.t) (states : state_mid IdMap.t)
    (state : state_mid) : state_tyd =
  let us = unloc state in
  let sc = make_state_context (unloc state) internal_ports kind in
  let sa = init_state_analysis sc in
  let ss = get_state_sigs states in
  let env = augment_env_with_state_context (top_env ()) sc in
  let code = check_state_code abip ss sc sa env us.mmclauses in
  let us' : state_body_tyd =
    {is_initial     = us.is_initial;
     params         = sc.params;
     vars           = sc.vars;
     internal_ports = sc.internal_ports;
     mmclauses      = code} in
  mk_loc (loc state) us'

(* check that all states are reachable from the initial state
   of otherwise checked states *)

let check_reachability (states : state_tyd IdMap.t) : unit =
  let rec closure olds nws =
    match nws with
    | []        -> IdSet.of_list olds
    | nw :: nws ->
      if List.mem nw olds
      then closure olds nws
      else let st = IdMap.find nw states in
           let nexts =
             IdSet.to_list (state_transitions_of_state st) in
           closure (olds @ [nw]) (nws @ nexts) in
  let init_id = initial_state_id_of_states states in
  let clos = closure [] [init_id] in
  if IdSet.cardinal clos <> IdMap.cardinal states
  then let fst_non_reach_id =
         List.hd
         (IdSet.to_list
          (IdSet.diff
           (IdSet.of_list (List.map fst (IdMap.bindings states)))
           clos)) in
       let fst_non_reach_st = IdMap.find fst_non_reach_id states in
       error_message (loc fst_non_reach_st)
       (fun ppf ->
          fprintf ppf
          "@[state@ %s@ is@ not@ reachable@ from@ initial@ state@]"
          fst_non_reach_id)

(* check the lower-level of a state_tyd IdMap.t state machine;
   used for states of both real and ideal functionalities, and
   simulators; kind will be RealPartyKind b (where b says if the
   party serves a basic adversarial interfadce), IdealKind or SimKind *)

let check_lowlevel_states
    (abip : all_basic_inter_paths) (kind : kind)
    (internal_ports : QidSet.t) (states : state_mid IdMap.t)
      : state_tyd IdMap.t =
  let states =
    IdMap.map
    (check_lowlevel_state abip kind internal_ports states)
    states
  in check_reachability states; states

(* this is for use in checking ideal functionalities and simulators;
   not used when checking parties of real functionalities;
   kind will be IdealKind or SimKind *)

let check_states
    (id : psymbol) (abip : all_basic_inter_paths) (kind : kind)
    (internal_ports : QidSet.t) (state_defs : state_def list)
      : state_tyd IdMap.t =
  let states = check_toplevel_states id state_defs in
  check_lowlevel_states abip kind internal_ports states

(**************************** functionality checks ****************************)

let filter_basic_inter_paths_by_serves
    (bips : basic_inter_path list) (serves : symbol list located list)
      : basic_inter_path list =
  List.filter
  (fun bip -> List.exists (fun serv -> unloc serv = fst bip) serves)
  bips

let get_all_external_basic_inter_paths
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (dirid : symbol) (advid : symbol option)
      : all_basic_inter_paths =
  let direct = get_basic_inter_paths_from_inter_id root dirid dir_inter_map in
  let adversarial =
    match advid with
    | Some id -> get_basic_inter_paths_from_inter_id root id adv_inter_map
    | None    -> [] in
  {direct = direct; adversarial = adversarial; internal = []}

let get_dir_inter_id_impl_by_fun_pair_id
    (fun_pid : symb_pair) (fun_map : fun_tyd IdPairMap.t) : symbol =
  let func = IdPairMap.find fun_pid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr  -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

(* does *not* take a real_fun_body_tyd or fun_body_tyd as a parameter,
   because we need to call function before these are constructed; but
   *does* take some components of real_fun_body_tyd *)

let get_all_basic_inter_paths_of_real_fun_party
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (fun_map : fun_tyd IdPairMap.t) (dirid : symbol) (advid : symbol option)
    (params : (symb_pair * int) IdMap.t)
    (sub_funs : symb_pair IdMap.t) (serves : symbol list located list)
      : all_basic_inter_paths =
  let abips =
    get_all_external_basic_inter_paths root dir_inter_map
    adv_inter_map dirid advid in
  let dir_bips =
    filter_basic_inter_paths_by_serves abips.direct serves in
  let adv_bips =
    filter_basic_inter_paths_by_serves abips.adversarial serves in
  let param_bips_map =
    IdMap.mapi
    (fun pid (x : symb_pair * int) ->
       let root' = fst (fst x) in
       let inter_id = snd (fst x) in
       get_basic_inter_paths root' pid inter_id dir_inter_map)
    params in
  let sub_fun_bips_map =
    IdMap.mapi
    (fun sfid (pid : symb_pair) ->
       let dirid = get_dir_inter_id_impl_by_fun_pair_id pid fun_map in
       let root' = fst pid in
       get_basic_inter_paths root' sfid dirid dir_inter_map)
    sub_funs in
  let internal_bips_map =
    IdMap.union
    (fun _ _ _ -> failure "impossible - params and subfuns disjoint")
    param_bips_map sub_fun_bips_map in
  let internal = IdMap.fold (fun _ bips l -> l @ bips) internal_bips_map [] in
  {direct = dir_bips; adversarial = adv_bips; internal = internal}

type party_body_mid =
  {serves : symbol list located list;  (* what interfaces served by party *)
   states : state_mid IdMap.t}         (* state machine *)

type party_mid = party_body_mid located

let check_toplevel_party
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t) (id_dir_inter : symbol)
    (id_adv_inter : symbol option) (pd : party_def) : party_mid =
  let pqsymbol2sll (pqs : pqsymbol) : symbol list located =
    let qs = unloc pqs in
    mk_loc (loc pqs) (fst qs @ [snd qs]) in
  let serves = List.map pqsymbol2sll pd.serves in
  let () =
    List.iter
    (check_inter_id_path root id_dir_inter id_adv_inter
     dir_inter_map adv_inter_map)
    serves in
  let () = check_served_inter_id_paths serves in
  let states = check_toplevel_states pd.id pd.states in
  mk_loc (loc pd.id) {serves = serves; states = states}

let check_parties_serve_coverage_and_distinct
    (root : symbol) (parties : party_mid IdMap.t)
    (id_dir_inter : symbol) (id_adv_inter : symbol option)
    (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t) : unit =
  let served_ps =
    IdMap.fold (fun _ p l -> l @ (unloc p).serves) parties [] in
  let () =
    check_inter_id_paths_unique
    (fun ppf ->
       fprintf ppf
       "@[parties@ must@ serve@ distinct@ sub-interfaces@]")
    served_ps in
  check_inter_id_paths_coverage root id_dir_inter id_adv_inter
  dir_inter_map adv_inter_map served_ps

let check_toplevel_parties
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (id_dir_inter : symbol) (id_adv_inter : symbol option)
    (party_defs : party_def IdMap.t)
      : party_mid IdMap.t =
  let parties =
    IdMap.map
    (check_toplevel_party root dir_inter_map adv_inter_map id_dir_inter
     id_adv_inter)
    party_defs in
  let () =
    check_parties_serve_coverage_and_distinct root parties
    id_dir_inter id_adv_inter dir_inter_map adv_inter_map in
  parties

let check_lowlevel_party
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (fun_map : fun_tyd IdPairMap.t) (id_dir_inter : symbol)
    (id_adv_inter : symbol option) (internal_ports : QidSet.t)
    (params : (symb_pair * int) IdMap.t)
    (sub_funs : symb_pair IdMap.t) (pdt : party_mid) : party_tyd =
  let updt = unloc pdt in
  let abip =
    get_all_basic_inter_paths_of_real_fun_party root
    dir_inter_map adv_inter_map fun_map id_dir_inter id_adv_inter
    params sub_funs updt.serves in
  let serves_basic_adv =
    match id_adv_inter with
    | None              -> false
    | Some id_adv_inter ->
        Option.is_some
        (List.find_opt
         (fun x -> List.hd (unloc x) = id_adv_inter)
         updt.serves) in
  let states =
    check_lowlevel_states abip (RealPartyKind serves_basic_adv)
    internal_ports updt.states in
  let serves = updt.serves in
  let ret : party_body_tyd = {serves = serves; states = states} in
  mk_loc (loc pdt) ret

let check_parties
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t)
    (fun_map : fun_tyd IdPairMap.t) (id_dir_inter : symbol)
    (id_adv_inter : symbol option) (params : (symb_pair * int) IdMap.t)
    (sub_funs : symb_pair IdMap.t) (party_defs : party_def IdMap.t)
      : party_tyd IdMap.t =
  let internal_ports = get_keys_as_sing_qids party_defs in
  let parties_mid =
    check_toplevel_parties root dir_inter_map adv_inter_map id_dir_inter
    id_adv_inter party_defs in
  IdMap.map
      (check_lowlevel_party root dir_inter_map adv_inter_map fun_map
      id_dir_inter id_adv_inter internal_ports params sub_funs)
    parties_mid

let check_real_fun_params
    (root : symbol) (dir_inter_map : inter_tyd IdPairMap.t)
    (adv_inter_map : inter_tyd IdPairMap.t) (params : fun_param list)
      : (symb_pair * int) IdMap.t =
  let check_real_fun_param (param : fun_param) : symb_pair * int =
    let pid =
      check_exists_inter_qid DirectInterKind root
      dir_inter_map param.dir_qid in
    let () =
      check_is_composite_id_pair root DirectInterKind dir_inter_map pid in
    let () =
      if exists_id_pair_inter_maps dir_inter_map adv_inter_map
         (root, unloc param.id)
      then error_message (loc param.id)
           (fun ppf ->
              fprintf ppf
              ("@[functionality@ parameter@ name@ may@ not@ be@ same@ " ^^
               "as@ top-level@ interface@ name@]")) in
     (unloc pid, index_of_ex param params) in
  let param_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ functionality@ parameter@ name@]")
    params (fun p -> p.id) in
  IdMap.map check_real_fun_param param_map

let check_exists_fun_qid
    (root : symbol) (fun_map : fun_tyd IdPairMap.t)
    (qid : pqsymbol) : symb_pair located =
  let uqid = unloc qid in
  let l = loc qid in
  match uqid with
  | ([], uid)   ->
      if exists_id_pair fun_map (root, uid)
      then mk_loc l (root, uid)
      else error_message l
           (fun ppf ->
              fprintf ppf
              "@[functionality@ does@ not@ exist:@ %s@]" uid)
  | ([rt], uid) ->
      if exists_id_pair fun_map (rt, uid)
      then mk_loc l (rt, uid)
      else error_message l
           (fun ppf ->
              fprintf ppf
              "@[functionality@ does@ not@ exist:@ %a@]" pp_qsymbol uqid)
  | _           ->
      error_message l
      (fun ppf ->
         fprintf ppf
         "@[invalid@ form@ for@ functionality@ name:@ %a@]" pp_qsymbol uqid)

let check_fun (root : symbol) (maps : maps_tyd) (fund : fun_def) : fun_tyd =
  let () =
    check_exists_inter_id DirectInterKind root maps.dir_inter_map fund.dir_id in
  let () =
    check_is_composite_id DirectInterKind root maps.dir_inter_map fund.dir_id in
  let uid_dir_inter = unloc fund.dir_id in
  let uid_adv_inter =
    match fund.adv_id with
    | None    -> None
    | Some id ->
        (check_exists_inter_id AdversarialInterKind root maps.adv_inter_map id;
         Some (unloc id)) in
  match fund.fun_body with
  | FunBodyReal fbr ->
      let () =
        match fund.adv_id with
        | None    -> ()
        | Some id ->
            check_is_composite_id AdversarialInterKind root
            maps.adv_inter_map id in
      let params =
        check_real_fun_params root maps.dir_inter_map maps.adv_inter_map
        fund.params in
      let sub_fun_decls =
        check_unique_ids
        (fun ppf -> fprintf ppf "@[duplicate@ subfunctionality@ name@]")
        fbr.sub_fun_decls (fun x -> x.id) in
      let () =
        let dup_ids =
          IdMap.filter (fun id _ -> IdMap.mem id params) sub_fun_decls in
        if IdMap.is_empty dup_ids then ()
        else let id, dup = IdMap.choose dup_ids in
             error_message (loc dup.id)
             (fun ppf ->
                fprintf ppf
                ("@[the@ name@ %s@ is@ the@ same@ name@ as@ one@ of@ the@ " ^^
                 "functionality's@ parameters@]")
                id) in
      let check_sub_fun_decl (sf : sub_fun_decl) : symb_pair =
        let uid = unloc sf.id in
        let fun_pid =
          check_exists_fun_qid root maps.fun_map sf.fun_qid in
        let ft = IdPairMap.find (unloc fun_pid) maps.fun_map in
        let fbt = unloc ft in
        if uid = unloc fund.id
          then error_message (loc sf.id)
               (fun ppf ->
                  fprintf ppf
                  ("@[subfunctionality@ name@ may@ not@ be@ same@ " ^^
                   "as@ real@ functionality@ name@]"))
        else if exists_id_pair_inter_maps maps.dir_inter_map
                maps.adv_inter_map (root, uid)
          then error_message (loc sf.id)
               (fun ppf ->
                  fprintf ppf
                  ("@[subfunctionality@ name@ may@ not@ be@ same@ as@ " ^^
                   "top-level@ interface@ name@]"))
        else if is_real_fun_body_tyd fbt
          then error_message (loc fun_pid)
               (fun ppf ->
                  fprintf ppf
                  "@[%a@ is@ not@ an@ ideal@ functionality@]"
                  (pp_id_pair_abbrev root) (unloc fun_pid))
        else unloc fun_pid in
      let sub_funs = IdMap.map check_sub_fun_decl sub_fun_decls in
      let party_defs =
        check_unique_ids
        (fun ppf -> fprintf ppf "@[duplicate@ party@ name@]")
        fbr.party_defs (fun x -> x.id) in
      let parties =
        check_parties root maps.dir_inter_map maps.adv_inter_map maps.fun_map
        uid_dir_inter uid_adv_inter params sub_funs party_defs in
      let fbrt =
        {params = params; id_dir_inter = uid_dir_inter;
         id_adv_inter = uid_adv_inter; sub_funs = sub_funs;
         parties = parties} in
      let funbody = FunBodyRealTyd fbrt in
      mk_loc (loc fund.id) funbody
  | FunBodyIdeal state_defs ->
      let () =
        match fund.adv_id with
        | None    -> ()
        | Some id ->
            check_is_basic_id AdversarialInterKind root maps.adv_inter_map id in
      let abip =
        get_all_external_basic_inter_paths root maps.dir_inter_map
        maps.adv_inter_map uid_dir_inter uid_adv_inter in
      let ik =
        match fund.adv_id with
        | None   -> IdealNoAdvKind
        | Some _ -> IdealKind in
      let states =
        check_states fund.id abip ik QidSet.empty state_defs in
      let ifbt =
        {id_dir_inter = uid_dir_inter; id_adv_inter = uid_adv_inter;
         states = states} in
      let funbody = FunBodyIdealTyd ifbt in
      mk_loc (loc fund.id) funbody

let check_fun_def
    (root : symbol) (maps : maps_tyd) (fund : fun_def) : maps_tyd =
  let uid = unloc fund.id in
  let () =
    if exists_id_pair_maps_tyd maps (root, uid)
    then error_message (loc fund.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let funt = check_fun root maps fund in
  {maps with
     fun_map = IdPairMap.add (root, uid) funt maps.fun_map}

(****************************** simulator checks ******************************)

let get_sim_components
    (root : symbol) (fun_map : fun_tyd IdPairMap.t) (sims : symbol)
    (sims_arg_pair_ids : symb_pair list) : (symbol * fun_body_tyd) QidMap.t =
  let sims_body = unloc (IdPairMap.find (root, sims) fun_map) in
  let qidmap_fun = QidMap.singleton [sims] (root, sims_body) in
  let qidmap_params =
    let pids =
      indexed_map_to_list_only_keep_keys
      (real_fun_body_tyd_of sims_body).params in
    List.fold_left2
    (fun mp pid pair_id ->
       let arg_body = unloc (IdPairMap.find pair_id fun_map) in
       QidMap.add [sims; pid] (fst pair_id, arg_body) mp)
    QidMap.empty pids sims_arg_pair_ids in
  let qidmap_subfuns =
    IdMap.fold
    (fun sfid ideal_fun_pair_id mp ->
       let ideal_body = unloc (IdPairMap.find ideal_fun_pair_id fun_map) in
       QidMap.add [sims; sfid] (fst ideal_fun_pair_id, ideal_body) mp)
    (real_fun_body_tyd_of sims_body).sub_funs QidMap.empty in
  let disj = (fun _ _ _ -> failure "cannot happen") in
  QidMap.union disj qidmap_fun
  (QidMap.union disj qidmap_params qidmap_subfuns)

let get_fun_adv_basic_inter_paths
    (adv_inter_map : inter_tyd IdPairMap.t)
    (comp : symbol * fun_body_tyd) : basic_inter_path list =
  match id_adv_inter_of_fun_body_tyd (snd comp) with
  | Some id ->
      get_basic_inter_paths_from_inter_id (fst comp) id adv_inter_map
  | None    -> []

let get_sim_basic_inter_id_paths
    (root : symbol) (adv_inter_map : inter_tyd IdPairMap.t) (uses : symbol)
    (comps : (symbol * fun_body_tyd) QidMap.t) : basic_inter_path list =
  let bips_comps_map =
    QidMap.map (get_fun_adv_basic_inter_paths adv_inter_map) comps in
  let bips_map =
    QidMap.add
    []
    (List.map invert_basic_inter_path
     (get_basic_inter_paths_from_inter_id root uses adv_inter_map))
    bips_comps_map in
  QidMap.fold
  (fun qid bips_of_qid bips ->
     bips @ List.map (fun bip -> (qid @ fst bip, snd bip)) bips_of_qid)
  bips_map []

let get_internal_ports (real_fun_body : real_fun_body_tyd) : QidSet.t =
  get_keys_as_sing_qids real_fun_body.parties

let get_sim_internal_ports
    (root : symbol) (fun_map : fun_tyd IdPairMap.t)
    (sims : symbol) : QidSet.t =
  let sims_rfbt =
    real_fun_body_tyd_of (unloc (IdPairMap.find (root, sims) fun_map)) in
  let int_ports = get_internal_ports sims_rfbt in
  QidSet.map (fun qid -> sims :: qid) int_ports

let check_exists_fun_id
    (root : symbol) (fun_map : fun_tyd IdPairMap.t) (funid : psymbol) : unit =
  let ufid = unloc funid in
  if exists_id_pair fun_map (root, ufid) then ()
  else error_message (loc funid)
       (fun ppf -> fprintf ppf "@[functionality@ isn't@ defined:@ %s@]" ufid)

let check_exists_and_is_real_fun
    (root : symbol) (funs : fun_tyd IdPairMap.t) (funid : psymbol) =
  let () = check_exists_fun_id root funs funid in
  let f = unloc (IdPairMap.find (root, unloc funid) funs) in
  if not (is_real_fun_body_tyd f)
  then error_message (loc funid)
       (fun ppf ->
          fprintf ppf
          "@[the@ simulated@ functionality@ must@ be@ a@ real@ functionality@]")

let get_dir_interface_pair_ids_of_params_of_real_fun_id
    (fun_map : fun_tyd IdPairMap.t) (funid : symb_pair)
      : symb_pair list =
  let func = IdPairMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr -> indexed_map_to_list fbr.params
  | FunBodyIdealTyd _  -> failure "cannot happen - will be real functionality"

let get_dir_interface_pair_ids_of_params_of_real_fun_id_root
    (root : symbol) (fun_map : fun_tyd IdPairMap.t)
    (funid : symbol) : symb_pair list =
  get_dir_interface_pair_ids_of_params_of_real_fun_id fun_map (root, funid)

let check_sims_fun_args
    (root : symbol) (fun_map : fun_tyd IdPairMap.t) (sims : psymbol)
    (sims_args : symb_pair located list located) : unit =
  let params_dir_pair_ids =
    get_dir_interface_pair_ids_of_params_of_real_fun_id_root root fun_map
    (unloc sims) in
  let args_dir_pair_ids =
    List.map
    (fun pair_id ->
       (fst pair_id, get_dir_inter_id_impl_by_fun_pair_id pair_id fun_map))
    (unlocs (unloc sims_args)) in
  let () =
    List.iter
    (fun pid ->
       let funb = unloc (IdPairMap.find (unloc pid) fun_map) in
       match funb with
       | FunBodyRealTyd _ ->
           error_message (loc pid)
           (fun ppf ->
              fprintf ppf
              ("@[the@ argument@ to@ simulated@ functionality@ must@ " ^^
               "be@ an@ ideal@ functionality@]"))
       | FunBodyIdealTyd _  ->
           (* we know the ideal functionality implements a basic
              adversarial interface *)
           ())
    (unloc sims_args) in
  let () =
    if List.length params_dir_pair_ids <> List.length args_dir_pair_ids
    then error_message (loc sims_args)
         (fun ppf ->
            fprintf ppf
            "@[wrong@ number@ of@ arguments@ for@ functionality@]") in
  List.iteri
  (fun i pair_id ->
     if List.nth params_dir_pair_ids i <> List.nth args_dir_pair_ids i
     then error_message (loc pair_id)
          (fun ppf ->
             fprintf ppf
             ("@[argument@ %d@ implements@ composite@ direct@ " ^^
              "interface@ %a,@ whereas@ it@ should@ implement@ %a@]")
             (i + 1)
             (pp_id_pair_abbrev root) (List.nth args_dir_pair_ids i)
             (pp_id_pair_abbrev root) (List.nth params_dir_pair_ids i)))
  (unloc sims_args)

let check_sim
    (root : symbol) (adv_inter_map : inter_tyd IdPairMap.t)
    (fun_map : fun_tyd IdPairMap.t) (sd : sim_def) : sim_tyd =
  let () =
    check_exists_inter_id AdversarialInterKind root adv_inter_map sd.uses in
  let () = check_is_basic_id AdversarialInterKind root adv_inter_map sd.uses in
  let uses = unloc sd.uses in
  let () = check_exists_and_is_real_fun root fun_map sd.sims in
  let sims = unloc sd.sims in
  let sims_args =
    mk_loc (loc sd.sims_arg_qids)
    (List.map (check_exists_fun_qid root fun_map) (unloc sd.sims_arg_qids)) in
  let () = check_sims_fun_args root fun_map sd.sims sims_args in
  let sims_arg_pair_ids = unlocs (unloc sims_args) in
  let internal_ports = get_sim_internal_ports root fun_map sims in
  let comps = get_sim_components root fun_map sims sims_arg_pair_ids in
  let bips = get_sim_basic_inter_id_paths root adv_inter_map uses comps in
  let abip = {direct = []; adversarial = bips; internal = []} in
  let states = check_states sd.id abip SimKind internal_ports sd.states in
  let sbt =
    {uses = uses; sims = sims; sims_arg_pair_ids = sims_arg_pair_ids;
     states = states} in
  mk_loc (loc sd.id) sbt

let check_sim_def
    (root : symbol) (maps : maps_tyd) (simd : sim_def) : maps_tyd =
  let uid = unloc simd.id in
  let () =
    if exists_id_pair_maps_tyd maps (root, uid)
    then error_message (loc simd.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let sdt = check_sim root maps.adv_inter_map maps.fun_map simd in
  {maps with
     sim_map = IdPairMap.add (root, uid) sdt maps.sim_map}

(***************************** definition checks ******************************)

let check_defs root maps defs =
  let check_def maps def =
    match def with
    | InterDef interd -> check_inter_def root maps interd
    | FunDef fund     -> check_fun_def root maps fund
    | SimDef simd     -> check_sim_def root maps simd in
  List.fold_left check_def maps defs

(**************************** specification checks ****************************)

(* when merging maps, there will never be disagreement in cases when
   an id pair or id is in the domain of both maps *)

let union_maps (oldmap : maps_tyd) (newmap : maps_tyd) : maps_tyd =
  {dir_inter_map =
     IdPairMap.union
     (fun _ x y -> assert (x = y); Some x)
     oldmap.dir_inter_map newmap.dir_inter_map;
   adv_inter_map =
     IdPairMap.union
     (fun _ x y -> assert (x = y); Some x)
     oldmap.adv_inter_map newmap.adv_inter_map;
   fun_map =
     IdPairMap.union
     (fun _ x y -> assert (x = y); Some x)
     oldmap.fun_map newmap.fun_map;
   sim_map =
     IdPairMap.union
     (fun _ x y -> assert (x = y); Some x)
     oldmap.sim_map newmap.sim_map;
   uc_reqs_map =
     IdMap.union
     (fun _ x y -> assert (x = y); Some x)
     oldmap.uc_reqs_map newmap.uc_reqs_map;
   ec_reqs_map =
     IdMap.union
     (fun _ x y -> assert (x = y); Some x)
     oldmap.ec_reqs_map newmap.ec_reqs_map;
   ec_scope_map =
     IdMap.union
     (fun _ x y -> assert (x == y); Some x)
     oldmap.ec_scope_map newmap.ec_scope_map}

let load_uc_req
    (check_id : psymbol -> maps_tyd) (maps : maps_tyd) (id : psymbol)
      : maps_tyd =
  let uid = unloc id in
  if not (Char.is_uppercase uid.[0])
  then error_message (loc id)
       (fun ppf ->
          fprintf ppf
          ("@[UC@ (.uc)@ file@ to@ be@ required@ must@ begin@ " ^^
           "with@ uppercase@ letter:@ %s@]")
          uid)
  else let () = UcStackedScopes.new_scope () in
       let maps' = check_id id in
       let maps = union_maps maps maps' in
       let () = UcStackedScopes.end_scope () in
       maps

let load_uc_reqs
    (root : symbol) (check_id : psymbol -> maps_tyd) (maps : maps_tyd)
    (reqs : psymbol list) : maps_tyd =
  let maps = List.fold_left (load_uc_req check_id) maps reqs in
  {maps with uc_reqs_map =
     IdMap.update root
     (fun sym_opt ->
        match sym_opt with
        | None   -> Some (List.map unloc reqs)
        | Some _ -> failure "cannot happen")
     maps.uc_reqs_map}

let load_ec_reqs (reqs : (string located * bool) list)
      : (string * bool) list =
  (* last require import will be prelude/UCBasicTypes.ec *)
  let reqs = reqs @ [(mk_loc _dummy "UCBasicTypes", true)] in
  let reqimp (id, imp) =
    let uid = unloc id in
    let () =
      if not (Char.is_uppercase uid.[0])
      then error_message (loc id)
           (fun ppf ->
              fprintf ppf
              ("@[EasyCrypt@ theory@ to@ be@ imported@ must@ begin@ with@ " ^^
               "uppercase@ letter:@ %s@]")
              uid) in
    UcEcInterface.require id (if imp then Some `Import else None) in
  List.iter reqimp reqs;
  List.map (fun (id, b) -> unloc id, b) reqs

let check_units_subfuns (root : string) (maps : maps_tyd) (rf : fun_tyd) =
  let check_units_subfun sfid (root', ifid) =
    (* root' will already have been checked to be a valid unit,
       unless it's the current file, in which case all but the
       subfunctionality and parameter checks will have been completed *)
    if root' = root
    then error_message (loc rf)
         (fun ppf ->
            fprintf ppf
            ("@[subfunctionality@ %s@ of@ real@ functionality@ must@ "   ^^
             "come@ from@ different@ unit@ than@ real@ functionality,@ " ^^
             "but@ this@ is@ not@ true@ for@ %a@]")
            sfid (pp_id_pair_abbrev root) (root', ifid));
    if is_triple_unit root' maps
    then error_message (loc rf)
         (fun ppf ->
            fprintf ppf
            ("@[subfunctionality@ %s@ of@ real@ functionality@ must@ " ^^
             "be@ ideal@ functionality@ of@ unit@ with@ only@ ideal@ " ^^
             "functionality,@ but@ %a@ is@ not@ such@ an@ ideal@ "     ^^
             "functionality@]")
            sfid pp_id_pair (root', ifid)) in
  let rfbt = real_fun_body_tyd_of (unloc rf) in
  let sub_funs = rfbt.sub_funs in
  IdMap.iter check_units_subfun sub_funs

let check_units_params (root : string) (maps : maps_tyd) (rf : fun_tyd) =
  let check_units_param paramid ((root', dirid), _) =
    (* root' will already have been checked to be a valid unit, unless
       it's the current file, in which case all but the parameter
       checks will have been completed *)
    if root' = root
    then error_message (loc rf)
         (fun ppf ->
            fprintf ppf
            ("@[composite@ direct@ interface@ %a@ of@ parameter@ %s@ " ^^
             "of@ real@ functionality@ must@ come@ from@ different@ "  ^^
             "unit@ than@ real@ functionality@]")
            (pp_id_pair_abbrev root) (root', dirid) paramid);
    if is_singleton_unit root' maps
    then error_message (loc rf)
         (fun ppf ->
            fprintf ppf
            ("@[composite@ direct@ interface@ %a@ of@ parameter@ %s@ " ^^
             "of@ real@ functionality@ must@ come@ from@ unit@ with@ "     ^^
             "real@ functionality,@ ideal@ functionality@ and@ "           ^^
             "simulator@]")
            (pp_id_pair_abbrev root) (root', dirid) paramid) in
  let rfbt = real_fun_body_tyd_of (unloc rf) in
  let params = rfbt.params in
  IdMap.iter check_units_param params

let check_units
    (root : symbol) (qual_file : string) (maps : maps_tyd) : unit =
  let inter_names   = inter_names root maps in
  let rf_names      = real_fun_names root maps in
  let if_names      = ideal_fun_names root maps in
  let sim_names     = sim_names root maps in
  let num_rf_names  = IdSet.cardinal rf_names in
  let num_if_names  = IdSet.cardinal if_names in
  let num_sim_names = IdSet.cardinal sim_names in
  if num_rf_names  = 0 &&  (* singleton unit *)
     num_if_names  = 1 &&
     num_sim_names = 0
    then let inter_names_reach =
           inter_names_reach_fun root maps (IdSet.min_elt if_names) in
         let extra_inter = IdSet.diff inter_names inter_names_reach in
         match IdSet.min_elt_opt extra_inter with
         | None       -> ()
         | Some ex_id ->
             error_message (begin_of_file_loc qual_file)
             (fun ppf ->
                fprintf ppf
                ("@[file@ with@ root@ %s@ is@ not@ a@ valid@ unit@ " ^^
                 "because@ interface@ %s@ is@ extraneous@]")
                root ex_id)
  else if num_rf_names  = 1 &&  (* triple unit *)
          num_if_names  = 1 &&
          num_sim_names = 1
    then let rf_name = IdSet.min_elt rf_names in
         let rf = IdPairMap.find (root, rf_name) maps.fun_map in
         let if_name = IdSet.min_elt if_names in
         let i_f = IdPairMap.find (root, if_name) maps.fun_map in
         let sim_name = IdSet.min_elt sim_names in
         let sim = IdPairMap.find (root, sim_name) maps.sim_map in
         let inter_names_reach =
           IdSet.union
           (inter_names_reach_fun root maps rf_name)
           (IdSet.union
            (inter_names_reach_fun root maps if_name)
            (inter_names_reach_sim root maps sim_name)) in
         let extra_inter = IdSet.diff inter_names inter_names_reach in
         (* from above we know that: (unloc sim).sims = rf_name,
            as otherwise there wouldn't be a single real functionality *)
         if id_dir_inter_of_fun_body_tyd (unloc rf) <>
            id_dir_inter_of_fun_body_tyd (unloc i_f)
           then error_message (begin_of_file_loc qual_file)
                (fun ppf ->
                   fprintf ppf
                   ("@[for@ file@ with@ root@ %s@ to@ be@ a@ unit,@ " ^^
                    "real@ and@ ideal@ functionalities@ must@ have@ " ^^
                    "the@ same@ composite@ direct@ interfaces@]")
                   root)
         else if id_adv_inter_of_fun_body_tyd (unloc i_f) <>
                 Some (unloc sim).uses
           then error_message (begin_of_file_loc qual_file)
                (fun ppf ->
                   fprintf ppf
                   ("@[for@ file@ with@ root@ %s@ to@ be@ a@ unit,@ " ^^
                    "ideal@ functionality's@ basic@ adversarial@ interface@ " ^^
                    "must@ be@ used@ by@ simulator@]")
                   root)
         else if IdSet.mem
                 (Option.get (id_adv_inter_of_fun_body_tyd (unloc i_f)))
                 (basic_adv_inter_names_of_real_fun root maps rf_name)
           then error_message (begin_of_file_loc qual_file)
                (fun ppf ->
                   fprintf ppf
                   ("@[for@ file@ with@ root@ %s@ to@ be@ a@ unit,@ " ^^
                    "ideal@ functionality's@ basic@ adversarial@ interface@ " ^^
                    "may@ not@ be@ component@ of@ composite@ adversarial@ " ^^
                    "interface@ of@ real@ functionality@]")
                   root)
         else let () =
                match IdSet.min_elt_opt extra_inter with
                | None       -> ()
                | Some ex_id ->
                    error_message (begin_of_file_loc qual_file)
                    (fun ppf ->
                       fprintf ppf
                       ("@[file@ with@ root@ %s@ is@ not@ a@ valid@ unit@ " ^^
                        "because@ interface@ %s@ is@ extraneous@]")
                       root ex_id) in
              check_units_subfuns root maps rf;
              check_units_params root maps rf;
  else error_message (begin_of_file_loc qual_file)
       (fun ppf ->
          fprintf ppf
          ("@[for@ file@ with@ root@ %s@ to@ be@ a@ valid@ unit,@ " ^^
           "either@ there@ must@ be:@ a@ single@ ideal@ functionality@ " ^^
           "and@ no@ real@ functionalities@ or@ simulators;@ or@ exactly@ " ^^
           "one@ real@ functionality,@ ideal@ functionality,@ and@ " ^^
           "simulator; instead@ it@ has@ %d@ real@ functionalities,@ " ^^
           "%d@ ideal@ functionalities,@ and@ %d@ simulators@]")
          root num_rf_names num_if_names num_sim_names)

let typecheck
    (qual_file : string) (check_id : psymbol -> maps_tyd)
    (spec : spec) : maps_tyd =
  let root = UcUtils.capitalized_root_of_filename_with_extension qual_file in
  let empty_maps =
    {dir_inter_map = IdPairMap.empty;
     adv_inter_map = IdPairMap.empty;
     fun_map       = IdPairMap.empty;
     sim_map       = IdPairMap.empty;
     uc_reqs_map   = IdMap.empty;
     ec_reqs_map   = IdMap.empty;
     ec_scope_map  = IdMap.empty} in
  let maps =
    load_uc_reqs root check_id empty_maps spec.externals.uc_requires in
  let ec_reqs = load_ec_reqs spec.externals.ec_requires in
  let maps =
    {maps with ec_reqs_map =
       IdMap.update root
       (fun sym_opt ->
          match sym_opt with
          | None   -> Some ec_reqs
          | Some _ -> failure "cannot happen")
       maps.ec_reqs_map} in
  let maps =
    try check_defs root maps spec.definitions with
    | TyError (l, env, tyerr) ->
        error_message l
        (fun ppf -> EcUserMessages.TypingError.pp_tyerror env ppf tyerr) in
  let maps =
    {maps with ec_scope_map =
       IdMap.update root
       (fun sym_opt ->
          match sym_opt with
          | None   -> Some (UcStackedScopes.current_scope ())
          | Some _ -> failure "cannot happen")
       maps.ec_scope_map} in
  let () =
    if UcState.get_units ()
    then check_units root qual_file maps in
  maps

(* Interpreter User Input

   units checking assumed to have been completed *)

let id_dir_inter_of_fet (maps : maps_tyd) (fet : fun_expr_tyd) : symb_pair =
  match fet with
  | FunExprTydReal (fun_id, _) ->
      let fbt = unloc (IdPairMap.find fun_id maps.fun_map) in
      (fst fun_id, id_dir_inter_of_fun_body_tyd fbt)
  | FunExprTydIdeal fun_id ->
      let fbt = unloc (IdPairMap.find fun_id maps.fun_map) in
      (fst fun_id, id_dir_inter_of_fun_body_tyd fbt)

let rec inter_check_fun_expr
    (root : symbol) (maps : maps_tyd) (fe : fun_expr) : fun_expr_tyd =
  match fe with
  | FunExprNoArgs pqsym      ->
      let fun_id_l = check_exists_fun_qid root maps.fun_map pqsym in
      let fun_id = unloc fun_id_l in
      let l = loc fun_id_l in
      (match unloc (IdPairMap.find fun_id maps.fun_map) with
       | FunBodyRealTyd rfbt ->
           if IdMap.is_empty (rfbt.params)
           then FunExprTydReal (fun_id, [])
           else error_message l
                (fun ppf ->
                   fprintf ppf
                   "@[real@ functionality@ missing@ arguments@]")
       | FunBodyIdealTyd _ -> FunExprTydIdeal fun_id)
  | FunExprArgs (pqsym, fes) ->
      let fun_id_l = check_exists_fun_qid root maps.fun_map pqsym in
      let fun_id = unloc fun_id_l in
      let l = loc fun_id_l in
      (match unloc (IdPairMap.find fun_id maps.fun_map) with
       | FunBodyRealTyd _  ->
           let params_dir_pair_ids =
             get_dir_interface_pair_ids_of_params_of_real_fun_id
             maps.fun_map fun_id in
           let fets =
             List.map
             (fun fe -> inter_check_fun_expr root maps fe)
             fes in
           let args_dir_pair_ids = List.map (id_dir_inter_of_fet maps) fets in
           if List.length params_dir_pair_ids <> List.length args_dir_pair_ids
           then error_message l
                (fun ppf ->
                   fprintf ppf
                   ("@[real@ functionality@ expects@ %d@ argument(s),@ " ^^
                    "but@ was@ applied@ to@ %d@ argument(s)@]")
                   (List.length params_dir_pair_ids)
                   (List.length args_dir_pair_ids))
           else List.iteri
                (fun i l ->
                   if List.nth params_dir_pair_ids i <>
                      List.nth args_dir_pair_ids i
                   then error_message l
                        (fun ppf ->
                           fprintf ppf
                           ("@[argument@ %d@ implements@ composite@ "       ^^
                            "direct@ interface@ %a,@ whereas@ it@ should@ " ^^
                            "implement@ %a@]")
                           (i + 1)
                           pp_id_pair (List.nth args_dir_pair_ids i)
                           pp_id_pair (List.nth params_dir_pair_ids i)))
                (List.map loc_of_fun_expr fes);
                FunExprTydReal (fun_id, fets)
       | FunBodyIdealTyd _ ->
           error_message l
           (fun ppf ->
              fprintf ppf
              ("@[ideal@ functionality@ cannot@ have@ " ^^
               "arguments@]")))

let inter_check_real_fun_expr
    (root : symbol) (maps : maps_tyd) (fe : fun_expr) : fun_expr_tyd =
  let fet = inter_check_fun_expr root maps fe in
  if is_real_at_top_fet fet
  then fet
  else error_message (loc_of_fun_expr fe)
       (fun ppf ->
          fprintf ppf
          "@[real@ functionality@ expected@]")

(* check type in environment, rejecting type variables *)

let inter_check_type (env : env) (pty : pty) : ty =
  let ue = unif_env () in
  transty tp_nothing env ue pty

(* if expct_ty_opt is Some ty, then ty must not have any unification
   or type variables *)

let inter_check_expr_ue
    (env : env) (ue : unienv) (pform : pformula) (expct_ty_opt : ty option)
      : form * ty =
  let form = trans_form_opt env ue pform None in
  let ty = form.f_ty in
  let () =
    match expct_ty_opt with
    | None          -> ()
    | Some expct_ty ->
        unify_or_fail env ue (loc pform) ~expct:expct_ty ty in
  (* replace unification variables in formula by types *)
  let uidmap =
    try EcUnify.UniEnv.close ue with
    | EcUnify.UninstanciateUni ->
        failure
        "should not happen: a top-level expression won't have type variables" in
  let ts = EcFol.Tuni.subst uidmap in
  let form = EcFol.Fsubst.f_subst ts form in
  (* update result type, using the expected type if supplied (which
     was assumed to have no unification or type variables), and otherwise
     applying the result of the unification to ty *)
  let res_ty =
    match expct_ty_opt with
    | None          -> EcFol.ty_subst ts ty
    | Some expct_ty -> expct_ty in
  (form, res_ty)

let inter_check_expr (env : env) (pform : pformula) (expct_ty_opt : ty option)
      : form * ty =
  let ue = unif_env () in
  inter_check_expr_ue env ue pform expct_ty_opt

let inter_check_expr_port_or_addr
    (env : env) (ue : unienv) (poa : port_or_addr)
    (pi_opt : int option) : form =
  match poa with
  | PoA_Port pexpr ->
      let (form, _) = inter_check_expr_ue env ue pexpr (Some port_ty) in
      form
  | PoA_Addr pexpr ->
      match pi_opt with
      | None    ->
          error_message (loc pexpr)
          (fun ppf ->
             fprintf ppf
             "@[unable@ to@ infer@ port@ index@ of@ addr@]")
      | Some pi ->
          let (form, _) = inter_check_expr_ue env ue pexpr (Some addr_ty) in
          (f_tuple [form; f_int (EcBigInt.of_int pi)])

type msg_path_info =
  | MPI_Bad
  | MPI_BasicButPartOfComposite
  | MPI_Good of msg_mode * msg_dir * int * ty list

let inter_check_root_qualified_msg_path (maps : maps_tyd) (mp : msg_path_u)
      : msg_path_info =
  match mp.inter_id_path with
  | root :: top :: rest ->
      (let mode_pi_bibt_opt =
         match get_inter_tyd_mode maps root top with
         | None            -> None
         | Some (mode, it) ->
             match unloc it with
             | BasicTyd bibt        ->
                 if List.is_empty rest
                 then let uior = unit_info_of_root maps root in
                      if is_basic_adv_of_ideal_fun_of_unit uior top
                      then Some (mode, 1, bibt)
                      else Some (mode, 0, bibt)  (* part of composite *)
                 else None
             | CompositeTyd comp_mp ->
                 match rest with
                 | [sub] ->
                     (match IdMap.find_opt sub comp_mp with
                      | None     -> None
                      | Some bas ->
                          let it = Option.get (get_inter_tyd maps root bas) in
                          match unloc it with
                          | BasicTyd bibt  ->
                              let pi = id_map_ordinal1_of_sym comp_mp sub in
                              Some (mode, pi, bibt)
                          | CompositeTyd _ -> failure "cannot happen")
                 | _     -> None in
       match mode_pi_bibt_opt with
       | None                  -> MPI_Bad
       | Some (mode, pi, bibt) ->
           match IdMap.find_opt mp.msg bibt with
           | None     -> MPI_Bad
           | Some mbt ->
               if pi = 0
               then MPI_BasicButPartOfComposite
               else MPI_Good
                    (mode, mbt.dir, pi,
                     indexed_map_to_list (unlocm mbt.params_map)))
  | _                   -> MPI_Bad

let inter_check_sme
    (maps : maps_tyd) (env : env) (sme : sent_msg_expr) : sent_msg_expr_tyd =
  let ue = unif_env () in
  match sme with
  | SME_Ord sme    ->
      (let path = unloc (sme.path) in
       match inter_check_root_qualified_msg_path maps path with
       | MPI_Bad                           ->
           error_message (loc sme.path)
           (fun ppf ->
              fprintf ppf
              "@[%a@ is@ not@ a@ root-qualified@ message@ path@]"
              pp_qsymbol (msg_path_u_to_qsymbol path))
       | MPI_BasicButPartOfComposite       ->
           error_message (loc sme.path)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ %a@ goes@ through@ basic@ interface,@ " ^^
               "and@ instead@ must@ be@ expressed@ in@ terms@ of@ "      ^^
               "sub-interface@ of@ composite@ interface@]")
              pp_qsymbol (msg_path_u_to_qsymbol path))
       | MPI_Good (mode, dir, pi, exp_tys) ->
           let src_port_expr =
             inter_check_expr_port_or_addr env ue sme.src_poa
             (if pi <> 0 && dir = Out then Some pi else None) in
           let dest_port_expr =
             inter_check_expr_port_or_addr env ue sme.dest_poa
             (if pi <> 0 && dir = In then Some pi else None) in
           let args = unloc sme.args in
             if List.length exp_tys <> List.length args
             then error_message (loc sme.args)
                  (fun ppf ->
                     fprintf ppf
                     ("@[there@ are@ (is)@ %d@ argument(s),@ whereas@ " ^^
                      "there@ should@ be@ %d@ argument(s)@]")
                     (List.length args) (List.length exp_tys))
             else let exprs =
                    List.mapi
                    (fun i pexpr ->
                       let (ex, _) =
                         inter_check_expr_ue env ue pexpr
                         (Some (List.nth exp_tys i)) in
                       ex)
                    args in
                  SMET_Ord
                  {mode           = mode;
                   dir            = dir;
                   src_port_form  = src_port_expr;
                   path           = path;
                   args           = exprs;
                   dest_port_form = dest_port_expr})
  | SME_EnvAdv sme ->
      (let (src_port, _) =
         inter_check_expr_ue env ue sme.src_port (Some port_ty) in
       let (dest_port, _) =
         inter_check_expr_ue env ue sme.dest_port (Some port_ty) in
       SMET_EnvAdv
       {src_port_form  = src_port;
        dest_port_form = dest_port})

let inter_check_sent_msg_expr
    (maps : maps_tyd) (env : env) (sme : sent_msg_expr) : sent_msg_expr_tyd =
  try inter_check_sme maps env sme with
  | TyError (l, env, tyerr) ->
      error_message l
      (fun ppf -> EcUserMessages.TypingError.pp_tyerror env ppf tyerr)
