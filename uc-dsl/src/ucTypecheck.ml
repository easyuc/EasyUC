(* UcTypecheck module *)

(* Typecheck a specification *)

open Batteries
open EcLocation
open UcEcTypes
open UcTypes
open UcSpec
open UcTypedSpec
open UcUtils
open UcMessage

type maps_tyd =
  {dir_inter_map : inter_tyd IdMap.t;
   adv_inter_map : inter_tyd IdMap.t;
   fun_map       : fun_tyd IdMap.t;
   sim_map       : sim_def_tyd IdMap.t}

let exists_id_maps_tyd (maps : maps_tyd) (uid : string) =
  exists_id maps.dir_inter_map uid ||
  exists_id maps.adv_inter_map uid ||
  exists_id maps.fun_map uid ||
  exists_id maps.sim_map uid

(* convert a named list into an id map, checking for uniqueness
   of names; get_id returns the name of a list element *)

let check_unique_ids (msg : string) (al : 'a list) (get_id : 'a -> id)
                       : 'a IdMap.t = 
  let id_map = IdMap.empty in
  List.fold_left 
  (fun id_map a -> 
     let id_l = get_id a in 
     if exists_id id_map (unloc id_l) then 
       type_error (loc id_l) (msg ^ unloc id_l)
     else IdMap.add (unloc id_l) a id_map)
  id_map al

(* EasyCrypt type checks *)

let check_name_type_bindings (msg : string) (ntl : type_binding list)
      : typ_index IdMap.t = 
  let nt_map = check_unique_ids msg ntl (fun nt -> nt.id) in
  IdMap.map
  (fun (nt : type_binding) -> 
     mk_loc (loc nt.id) (check_type nt.ty, index_of_ex nt ntl))
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

let check_comp_item (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                    (ci : comp_item) : id = 
  let uid = unloc ci.inter_id in
  match IdMap.find_opt uid inter_map with
  | None    -> 
      type_error
      (loc ci.inter_id)
      (uid ^ " isn't " ^ inter_kind_to_str true ik ^ " interface name")
  | Some it ->
      let ibt = unloc it in
      if is_composite_tyd ibt
      then type_error (loc ci.inter_id) (uid ^ " isn't a basic interface")
      else mk_loc (loc ci.sub_id) (unloc ci.inter_id)

let check_basic_inter (mds : message_def list) : inter_body_tyd = 
  let msg_map =
    check_unique_ids "duplicate message name: " mds (fun md -> md.id) in
  BasicTyd
  (IdMap.map
   (fun (md : message_def) ->
      mk_loc
      (loc md.id)
      {dir = md.dir;
       params_map =
         check_name_type_bindings
         "duplicate message parameter name: " md.params;
       port = md.port})
  msg_map)

let check_comp_inter (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                     (cis : comp_item list) : inter_body_tyd = 
  let comp_item_map =
    check_unique_ids "duplicate sub-interface name: "
    cis (fun ci -> ci.sub_id) in
  CompositeTyd (IdMap.map (check_comp_item ik inter_map) comp_item_map)

let check_inter (e_maps : string -> bool) (ik : inter_kind)
                (inter_map : inter_tyd IdMap.t) (ni : named_inter) = 
  let uid = unloc ni.id in
  let () =
    if e_maps uid
    then type_error (loc ni.id)
         ("identifier already declared at top-level: " ^ uid) in
  let ibt =
    match ni.inter with
    | Basic mds     -> check_basic_inter mds
    | Composite cis -> check_comp_inter ik inter_map cis in
  let it = mk_loc (loc ni.id) ibt in
  IdMap.add uid it inter_map
                
let check_inter_def (maps : maps_tyd) interd : maps_tyd =
  let e_maps = exists_id_maps_tyd maps in
  match interd with
  | DirectInter ni      ->
      {maps with
         dir_inter_map =
           check_inter e_maps DirectInterKind maps.dir_inter_map ni}
  | AdversarialInter ni ->
      {maps with
         adv_inter_map =
           check_inter e_maps AdversarialInterKind maps.adv_inter_map ni}

let check_exists_inter (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                       (id : id) : unit = 
  let uid = unloc id in
  if exists_id inter_map uid then () 
  else type_error (loc id)
       (inter_kind_to_str false ik ^ " interface does not exist: " ^ uid)

(* the following two functions assume id exists in inter_map *)

let check_is_basic (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                   (id : id) : unit = 
  let uid = unloc id in
  match unloc (IdMap.find uid inter_map) with
  | BasicTyd _     -> ()
  | CompositeTyd _ ->
      type_error (loc id)
      (inter_kind_to_str false ik ^ " interface must be basic: " ^ uid)

let check_is_composite (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                       (id : id) : unit = 
  let uid = unloc id in
  match unloc (IdMap.find uid inter_map) with
  | BasicTyd _     ->
      type_error (loc id)
      (inter_kind_to_str false ik ^ " interface must be composite: " ^ uid)
  | CompositeTyd _ -> ()

(************************* real functionality checks **************************)

(* functionality parameter checking *)

let check_real_fun_params (dir_inter_map : inter_tyd IdMap.t)
                          (params : fun_param list) :
      (id * int) IdMap.t = 
  let check_real_fun_param (param : fun_param) : (id * int) = 
    let () = check_exists_inter DirectInterKind dir_inter_map param.id_dir in
    (check_is_composite DirectInterKind dir_inter_map param.id_dir;
     (mk_loc (loc param.id) (unloc param.id_dir),
      index_of_ex param params)) in
  let param_map =
    check_unique_ids "duplicate functionality parameter name: " params
    (fun p -> p.id) in
  IdMap.map check_real_fun_param param_map

(* checking the top-level only of a state machine

   does not descend into the message-matching clauses *)

let check_exactly_one_initial_state (id : id) (sds : state_def list) : id = 
  let inits =
        List.filter
        (fun sd ->
           match sd with
           | InitialState _ -> true
           | _              -> false)
        sds in
  match List.length inits with
  | 0 -> type_error (loc id) (unloc id ^ " doesn't have initial state")
  | 1 ->
      (match List.hd inits with
       | InitialState s   -> s.id
       | FollowingState _ ->
           UcMessage.failure "impossible, list contains only InitialState")
  | _ -> type_error (loc id) (unloc id ^ " has more than one initial state")

let check_toplevel_state (init_id : id) (st : state) : state_tyd = 
  let is_initial = (init_id = st.id) in
  let params =
    check_name_type_bindings "duplicate parameter name: " st.params in
  let vars =
    IdMap.map
    (fun ti -> mk_loc (loc ti) (fst (unloc ti)))
    (check_name_type_bindings "duplicate variable name: " st.code.vars) in
  let dup = IdMap.find_first_opt (fun uid -> IdMap.mem uid params) vars in
  match dup with
  | None        ->
      mk_loc (loc st.id)
      {is_initial = is_initial; params = params; vars = vars;
       mmclauses = st.code.mmclauses}
  | Some (uid, typ) ->
      type_error (loc typ)
      ("variable name " ^ uid ^ " is the same as one of the state's parameters")
                        
let drop_state_ctor (sd : state_def) : state = 
  match sd with 
  | InitialState s   -> s
  | FollowingState s -> s

(* id is name of party (in case of real functionality), ideal functionality,
   or simulator - only used for error messages *)

let check_toplevel_states (id : id) (states : state_def list)
                            : state_tyd IdMap.t = 
  let init_id = check_exactly_one_initial_state id states in
  let states = List.map (fun sd -> drop_state_ctor sd) states in
  let state_map =
    check_unique_ids "duplicate state name: " states (fun s -> s.id) in
  IdMap.map (check_toplevel_state init_id) state_map 

(* a basic_inter_path will have the form ([id1; id2], b) where

   id1 is the name of a composite interface, id2 is the name of one of
   that composite interface's sub-interfaces, and b is the basic
   interface (direct iff the composite interface is direct)
   corresponding to the functionality name that id2 is associated with
   in the composite interface; or

   id1 is the name of a subfunctionality of a real functionality,
   where the ideal functionality that id1 is an instance of implements
   a direct interface that is a composite interface, and id2 is the
   name of one of that composite interface's sub-interfaces, and b is
   the basic, direct interface corresponding to the functionality name
   that id2 is associated with in the composite interface *)

type basic_inter_path = string list * basic_inter_body_tyd

(* three kinds of basic_inter_path's - ones of a direct interface,
   ones of an adversarial interface, and internal ones (coming from a
   real functionality's subfunctionalities' direct interfaces) *)

type all_basic_inter_paths =
  {direct : basic_inter_path list; adversarial : basic_inter_path list;
   internal : basic_inter_path list}

let get_basic_inter_paths
    (root : string) (inter_id : string) (inter_map : inter_tyd IdMap.t)
      : basic_inter_path list =
  let getb_body (inter_id : string) : basic_inter_body_tyd = 
    let inter = IdMap.find inter_id inter_map in
    match (unloc inter) with
    | BasicTyd b -> b
    | _          ->
        failure
        ("cannot happen, this function is called only on basic interfaces") in
  let inter = IdMap.find inter_id inter_map in
  match unloc inter with
  | BasicTyd b         -> [([root], b)]
  | CompositeTyd cimap ->
      IdMap.fold
      (fun subid inter_id l ->
         ([root; subid], getb_body (unloc inter_id)) :: l)
      cimap []

let get_basic_inter_paths_from_inter_id
    (inter_id : string) (inter_map : inter_tyd IdMap.t)
      : basic_inter_path list =
  get_basic_inter_paths inter_id inter_id inter_map

let get_inter_id_paths_from_inter_id
    (inter_id : string) (inter_map : inter_tyd IdMap.t) : string list list = 
  List.map fst (get_basic_inter_paths_from_inter_id inter_id inter_map)

let get_fun_inter_id_paths
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t) :
      string list list = 
  let dir = get_inter_id_paths_from_inter_id id_dir_inter dir_inter_map in
  let adv =
        match id_adv_inter with
        | Some id -> get_inter_id_paths_from_inter_id id adv_inter_map
        | None    -> [] in
  dir @ adv

let check_id_paths_unique
    (msg : string) (idps : string list located list) : unit = 
  ignore
  (List.fold_left
   (fun l idp -> 
      let uidp = unloc idp in
      if List.mem uidp l
      then type_error (loc idp) msg
      else uidp :: l)
   [] idps)

let check_id_path
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t)
    (adv_inter_map : inter_tyd IdMap.t)
    (idp : id list) : string list located = 
  let uidp = unlocs idp in
  let loc = mergelocs idp in
  let ps =
    get_fun_inter_id_paths id_dir_inter id_adv_inter
    dir_inter_map adv_inter_map in
  if List.mem uidp ps
  then mk_loc loc uidp
  else let psf = List.filter (fun p -> List.tl p = uidp) ps in
       match List.length psf with
       | 0 ->
           type_error loc
           (string_of_id_path uidp ^
            " is not a part of the interfaces implemented by functionality")
       | 1 -> mk_loc loc (List.hd psf)  (* unambiguous *)
       | _ ->
           type_error loc
           (string_of_id_path uidp ^
            " is ambiguous, it is in both direct and adversarial interfaces " ^
            "implemented by functionality")

let check_served_paths (serves : string list located list)
                       (id_dir_inter : string) (party_id : id) : unit = 
  let er =
    ("a party can serve at most one basic direct interface and one " ^
     "basic adversarial interface") in
  let erone = "a party must serve one basic direct interface" in
  match List.length serves with
  | 0 -> type_error (loc party_id) erone
  | 1 ->
      if List.hd (unloc (List.nth serves 0)) = id_dir_inter
      then ()
      else type_error (loc (List.nth serves 0)) erone
  | 2 ->
      if List.hd (unloc (List.nth serves 0)) <>
         List.hd (unloc (List.nth serves 1))
      then ()
      else type_error (loc (List.nth serves 1)) er
  | _ -> type_error (mergelocs serves) er

(* check a party definition at the top-level (not below the level of
   message-matching clauses of states) only *)

let check_toplevel_party_def
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (pd : party_def) : party_def_tyd = 
  let serves =
    List.map
    (check_id_path id_dir_inter id_adv_inter dir_inter_map adv_inter_map)
    pd.serves in
  let () = check_served_paths serves id_dir_inter pd.id in
  let code = check_toplevel_states pd.id pd.states in
  mk_loc (loc pd.id) {serves = serves; states = code}
               
let check_id_paths_cover
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (served_ps : string list located list) : unit = 
  let serps = unlocs served_ps in
  let ps =
    get_fun_inter_id_paths id_dir_inter id_adv_inter
    dir_inter_map adv_inter_map in
  let unserved = List.filter (fun p -> not (List.mem p serps)) ps in
  if List.length unserved = 0
  then ()
  else type_error
       (mergelocs served_ps)
       ("these interfaces are not served by any party: " ^
        string_of_id_paths unserved)

let check_parties_serve_distinct_cover
    (parties : party_def_tyd IdMap.t)
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
      : unit = 
  let served_ps =
    IdMap.fold (fun _ p l -> l @ (unloc p).serves) parties [] in
  let () =
    check_id_paths_unique "parties must serve distinct interfaces"
    served_ps in
  check_id_paths_cover id_dir_inter id_adv_inter
  dir_inter_map adv_inter_map served_ps

let get_dir_inter_id_impl_by_fun
    (funid : string) (fun_map : fun_tyd IdMap.t) : string = 
  let func = IdMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

let get_param_dir_inter_ids
    (fun_map : fun_tyd IdMap.t) (funid : string) : string list = 
  let func = IdMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr -> unlocs (to_list fbr.params)
  | FunBodyIdealTyd _  -> []

type state_vars =
  {flags : string list; internal_ports : QidSet.t; consts : typ IdMap.t;
   vars : typ IdMap.t; initialized_vs : IdSet.t}

let init_state_vars (s : state_body_tyd) (ports : QidSet.t)
                    (flags : string list) : state_vars = 
  let consts = IdMap.map (fun p -> fst (unloc p)) s.params in
  let vars = IdMap.map (fun v -> unloc v) s.vars in
  {flags = flags; internal_ports = ports; consts = consts;
   vars = vars; initialized_vs = IdSet.empty}

type state_sig = typ list

let get_state_sig (s : state_body_tyd) : state_sig = 
  if s.is_initial then []
  else let ps = IdMap.bindings s.params in
       let ts = unlocs (snd (List.split ps)) in
       let tord = List.sort (fun t1 t2 -> snd t1 - snd t2) ts in
       (fst (List.split tord))

let get_state_sigs (states : state_tyd IdMap.t) : state_sig IdMap.t = 
  IdMap.map (fun s -> get_state_sig (unloc s)) states

let string_of_msg_path (mp : msg_path) : string = 
  let siop = string_of_id_path (unlocs mp.inter_id_path) in
  match mp.msg_or_other with 
  | MsgPathId id      -> siop ^ "." ^ unloc id
  | MsgPathOtherMsg _ -> siop ^ ".othermsg"

let string_of_msg_pathl (mpl : msg_path list) : string = 
  string_of_stringl (List.map (fun mp -> string_of_msg_path mp) mpl)

let filter_dir_basic_inter_paths
    (dir : msg_dir) (bips : basic_inter_path list) : basic_inter_path list = 
  List.map
  (fun bip ->
     (fst bip,
      IdMap.filter
      (fun _ md -> (unloc md).dir = dir)
      (snd bip)))
  bips

let get_incoming_msg_paths (abip : all_basic_inter_paths)
      : all_basic_inter_paths = 
  {direct      = filter_dir_basic_inter_paths In abip.direct;
   adversarial = filter_dir_basic_inter_paths In abip.adversarial;
   internal    = filter_dir_basic_inter_paths Out abip.internal}

let get_outgoing_msg_paths (abip : all_basic_inter_paths)
      : all_basic_inter_paths = 
  {direct      = filter_dir_basic_inter_paths Out abip.direct;
   adversarial = filter_dir_basic_inter_paths Out abip.adversarial;
   internal    = filter_dir_basic_inter_paths In abip.internal}

let msg_loc (mp : msg_path) : EcLocation.t = 
  match mp.msg_or_other with
  | MsgPathId id -> loc id
  | MsgPathOtherMsg l -> l

let msg_paths_of_b_inter_id_path (bp : basic_inter_path) : msg_path list =   
  IdMap.fold
  (fun id _ l ->
         { inter_id_path = dummylocl (fst bp);
           msg_or_other = MsgPathId (dummyloc id) } :: l)
  (snd bp) []

let mp_of_bpl (bpl : basic_inter_path list) : msg_path list = 
  List.flatten (List.map (fun bp -> msg_paths_of_b_inter_id_path bp) bpl)

let flatten_all_basic_inter_paths (abip : all_basic_inter_paths) : basic_inter_path list = 
  abip.direct @ abip.adversarial @ abip.internal

let msg_paths_of_all_basic_inter_paths (abip : all_basic_inter_paths) : msg_path list = 
  mp_of_bpl (flatten_all_basic_inter_paths abip)

let check_msg_path (abip : all_basic_inter_paths) (mp : msg_path) : msg_path = 
  let ips = mp_of_bpl abip.internal in
  let allps = msg_paths_of_all_basic_inter_paths abip in       
  let filter_by_msg_type (mt : id) (mpl : msg_path list) : msg_path list = 
    List.filter
    (fun p ->
       match p.msg_or_other with
       | MsgPathId mt' -> (unloc mt') = (unloc mt)
       | _             -> false)
    mpl in
  let filter_by_port_name_msg_type (pt : id) (mt : id)
                                   (mpl : msg_path list) : msg_path list = 
    filter_by_msg_type mt
    (List.filter
     (fun p ->
            unloc (List.hd(List.rev p.inter_id_path)) = unloc pt)
     mpl) in
  let unexpected() = 
    type_error (msg_loc mp)
               ("the message is unexpected. these messages are expected: " ^
                string_of_msg_pathl allps) in
  let ambiguous (mtch : msg_path list) = 
    type_error (msg_loc mp)
               ("the message is ambiguous. there are multiple messages " ^
                "that match the description: " ^ string_of_msg_pathl mtch) in
  let filtered (mtch : msg_path list) (imtch : msg_path list) : msg_path = 
    match List.length mtch with
    | 0 -> unexpected ()
    | 1 ->
        let l = merge (mergelocs mp.inter_id_path) (msg_loc mp) in
        if imtch = []
        then let ret = List.hd mtch in
               {inter_id_path =
                  List.map
                  (fun id -> mk_loc l (unloc id))
                  ret.inter_id_path;
                msg_or_other = mp.msg_or_other }
        else type_error l
             ("internal messages must have full paths. " ^
              "did you mean " ^ (string_of_msg_path (List.hd mtch)) ^
              " ?")
    | _ -> ambiguous mtch in
  match mp.msg_or_other with
  | MsgPathId mt -> 
      if List.exists
         (fun p -> string_of_msg_path p = string_of_msg_path mp)
         allps
      then mp
      else (match (List.length mp.inter_id_path) with
            | 0 -> let filter = filter_by_msg_type mt in
                   let mtch = filter allps in
                   let imtch = filter ips in
                   filtered mtch imtch
            | 1 -> let filter =
                     filter_by_port_name_msg_type (List.hd mp.inter_id_path) mt in
                   let mtch = filter allps in
                   let imtch = filter ips in
                   filtered mtch imtch
            | _ ->  unexpected ())
  | MsgPathOtherMsg _ ->
      if (List.exists
          (fun p -> qid1_starts_with_qid2 p.inter_id_path mp.inter_id_path)
          allps)
      then mp else unexpected ()

let remove_covered_paths (mps : msg_path list) (mp : msg_path) :
                           msg_path list = 
  let covered mp1 mp2 = 
    match mp2.msg_or_other with
    | MsgPathId _       -> string_of_msg_path mp1 = string_of_msg_path mp2
    | MsgPathOtherMsg _ ->
        qid1_starts_with_qid2 mp1.inter_id_path mp2.inter_id_path in
  let rem = List.filter (fun mp' -> not (covered mp' mp) ) mps in
  if List.length mps = List.length rem
  then type_error (msg_loc mp)
       ("this match is covered by previous matches and would never execute")
  else rem

let msg_paths_of_all_basic_inter_paths_w_othermsg (abip : all_basic_inter_paths) :
                                            msg_path list = 
  let mps = msg_paths_of_all_basic_inter_paths abip in
  let omps =
        List.map
        (fun bp ->
             { inter_id_path = dummylocl (fst bp);
               msg_or_other = MsgPathOtherMsg _dummy })
        (flatten_all_basic_inter_paths abip) in
  mps @ omps

let check_mm_ds_non_empty (abip : all_basic_inter_paths) (mpl : msg_path list) :
                            msg_path list = 
  let mps = msg_paths_of_all_basic_inter_paths_w_othermsg abip in
  List.fold_left (fun mps mp -> remove_covered_paths mps mp) mps mpl

let check_msg_match_deltas (abip : all_basic_inter_paths) (mml : msg_pat list) :
                             unit = 
  let mps = get_incoming_msg_paths abip in
  let r =
        check_mm_ds_non_empty
        mps (List.map (fun (mm : msg_pat) -> mm.path) mml) in
  if r<>[]
  then let l = msg_loc ((List.hd (List.rev mml)).path)
       in type_error l
          ("message match is not exhaustive, these " ^
           "messages are not matched: " ^ string_of_msg_pathl r)
  else ()

let check_types_compatible (vid : id) (vt : typ) (typ : typ) : unit = 
  if not (vt = typ)
  then type_error (loc vid)
       (unloc vid ^
        " doesn't have type compatible with " ^
        string_of_typ typ)

let get_declared_const_vars (sv : state_vars) = 
  IdMap.union
  (fun _ _ _ ->
     failure
     ("Impossible, we already checked params and local " ^
      "vars have different ids"))
  sv.consts sv.vars

let check_exists_and_has_compatible_type (vid : id) (typ : typ)
                                         (sv : state_vars) : unit = 
  let uvid = unloc vid in
  let pvs = get_declared_const_vars sv in
  if not (IdMap.mem uvid pvs)
  then type_error (loc vid)
       (uvid ^ " is neither a local variable nor a state parameter")
  else let vt = IdMap.find uvid pvs in
       check_types_compatible vid vt typ
        
let check_add_binding (vid : id) (sv : state_vars) : state_vars = 
  let uvid = unloc vid in
  if not (IdMap.mem uvid sv.vars)
  then type_error (loc vid)
       (uvid ^ " is not a local variable and values cannot be bound to it")
  else {flags = sv.flags; internal_ports = sv.internal_ports;
        consts = sv.consts; vars = sv.vars;
        initialized_vs = (IdSet.add uvid sv.initialized_vs)}

let check_type_add_binding (vid : id) (typ : typ) (sv : state_vars) :
                             state_vars = 
  (check_exists_and_has_compatible_type vid typ sv;
   check_add_binding vid sv)

let check_add_const (cid : id) (ct : typ) (valt : typ) (sv : state_vars) :
                      state_vars = 
  let () = check_types_compatible cid ct valt in
  let ucid = unloc cid in
  let pvs = get_declared_const_vars sv in
  if (IdMap.mem ucid pvs)
  then type_error (loc cid)
       ("duplicate occurrence of variable in pattern: " ^ ucid)
  else {flags = sv.flags; internal_ports = sv.internal_ports;
        consts = IdMap.add ucid ct sv.consts; vars = sv.vars;
        initialized_vs = sv.initialized_vs}

let check_port_var_binding (abip : all_basic_inter_paths) (mp : string list)
                           (vid : id) (sv : state_vars) : state_vars = 
  let d = List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) abip.direct in
  let i =
    List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) abip.internal in
  let a =
    List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) abip.adversarial in
  if not (d && not i && not a)
  then type_error (loc vid)
       ("the message " ^ string_of_id_path mp ^
        " maybe isn't an incoming message of a direct interface served by " ^
        "the party and cannot bind the source port to a variable")
  else check_add_const vid port_type port_type sv

let check_item_type_add_binding (sv : state_vars) (mi : pat)
                                (typ : typ) : state_vars = 
  match mi with
  | PatWildcard _   -> sv
  | PatId id     -> check_add_const id typ typ sv
  | PatIdType nt -> check_add_const nt.id (check_type nt.ty) typ sv

let rec get_loc_ty (ty : ty) : EcLocation.t = 
  match ty with
  | NamedTy id -> loc id
  | TupleTy tl -> mergeall (List.map (fun t -> get_loc_ty t) tl)

let get_loc_match_item (m_i : pat) : EcLocation.t = 
  match m_i with
  | PatWildcard l   -> l
  | PatId id     -> loc id
  | PatIdType nt -> merge (loc nt.id) (get_loc_ty nt.ty)

let get_loc_match_item_list (tm : pat list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_match_item mi) tm)

let check_msg_content_bindings
    (ps : basic_inter_path list) (mp : string list*string)
    (tm : pat list) (sv : state_vars) : state_vars = 
  let p = List.find (fun p -> (fst p) = (fst mp)) ps in
  let mt = to_list (unlocm((unloc(IdMap.find (snd mp) (snd p))).params_map)) in
  if List.length mt <> List.length tm
  then type_error (get_loc_match_item_list tm)
       ("the number of bindings is different then the number " ^
        "of message parameters")
  else List.fold_left2 check_item_type_add_binding sv tm mt

let check_pat_args (bips : basic_inter_path list) (mm : msg_pat)
                   (sv : state_vars) : state_vars = 
  match mm.pat_args with
  | None     -> sv
  | Some mil -> 
      match mm.path.msg_or_other with
      | MsgPathOtherMsg l ->
          type_error l
          ("othermsg cannot have value bindings. do you have " ^
           "redundant parenthesis?")
      | MsgPathId id      ->
          check_msg_content_bindings bips
          ((unlocs mm.path.inter_id_path),(unloc id)) mil sv

let check_match_bindings (abip : all_basic_inter_paths) (mm : msg_pat)
                         (sv : state_vars) : state_vars = 
  let sv' =        
    match mm.port_id with
    | Some id -> check_port_var_binding abip (unlocs mm.path.inter_id_path) id sv
    | None    -> sv in
  let ps = abip.direct @ abip.adversarial @ abip.internal in
  check_pat_args ps mm sv'

let get_var_type (sv : state_vars) (id : id) : typ = 
  let vs =
    IdMap.union
    (fun _ _ ->
       failure
       ("Impossible! we already checked that params and " ^
        "vars have different names"))
    sv.consts sv.vars in
  IdMap.find (unloc id) vs

let check_initialized (sv : state_vars) (id : id) : unit = 
  let uid = unloc id in
  if IdMap.mem uid sv.consts || IdSet.mem uid sv.initialized_vs then ()
  else type_error (loc id) (uid ^ " is not initialized")

let check_expr_var (sv : state_vars) (id : id) : typ = 
  let r = get_var_type sv id in
  let () = check_initialized sv id in
  r

let check_is_internal_port (sv : state_vars) (qid : qid) : bool =
  QidSet.mem (unlocs qid) sv.internal_ports

let check_qid_type (sv : state_vars) (qid : qid) : typ = 
  try
    (match qid with
     | id :: [] -> check_expr_var sv id
     | _        -> raise Not_found)
  with Not_found -> 
         if (check_is_internal_port sv qid) then port_type else raise Not_found

let check_expression (sv : state_vars) (expr : expression_l) : typ = 
  UcExpressions.check_expression (check_qid_type sv) expr

let check_val_assign (sv : state_vars) (vid : id) (ex : expression_l) :
                       state_vars = 
  let etyp = check_expression sv ex in
  check_type_add_binding vid etyp sv

let check_sampl_assign (sv : state_vars) (vid : id) (ex : expression_l) :
                         state_vars = 
  let etyp = check_expression sv ex in
  if not (UcExpressions.is_distribution etyp)
  then type_error (loc ex) ("you can sample only from distributions")
  else let dtyp = UcExpressions.get_distribution_typ etyp in 
       check_type_add_binding vid dtyp sv

let check_transition (si : state_expr) (ss : state_sig IdMap.t)
                     (sv : state_vars) : unit = 
  let ssig = 
    try IdMap.find (unloc(si.id)) ss with
      Not_found ->
        type_error (loc si.id) ("non-existing state: " ^ unloc si.id) in
  let sp = ssig and args = si.args in
  if List.length sp <> List.length args
  then type_error (loc si.id) "wrong number of arguments"
  else let te = List.combine sp args in
       List.iteri
       (fun i (sigt, sip) -> 
              let et = check_expression sv sip in
              if sigt <> et && sigt <> univ_type
              then type_error (loc sip)
                   (string_of_int (i+1) ^ ". parameter of state " ^
                    unloc si.id ^ " has type " ^ string_of_typ sigt ^
                    ", which is incompatible with type " ^
                    string_of_typ et ^ " of provided argument")
              else ())
       te

let check_msg_content_values (es : expression_l list) (mc : typ_index IdMap.t)
                             (sv : state_vars) : unit = 
  let sg = to_list (unlocm mc) in
  let esl = mergelocs es in
  if List.length es <> List.length sg
  then type_error esl "parameter number mismatch"
  else List.iter2
       (fun ex typ ->
              if not (check_expression sv ex = typ)
              then type_error (loc ex) ("parameter type mismatch"))
       es sg

let check_send_direct (msg : msg_expr) (mc : typ_index IdMap.t)
                      (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_id with
    | Some p ->
        (check_exists_and_has_compatible_type p port_type sv;
         check_initialized sv p)
    | None   -> type_error l ("missing destination port") in
  check_msg_content_values msg.args mc sv

let check_send_adversarial (msg : msg_expr) (mc : typ_index IdMap.t)
                           (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_id with
    | Some _ ->
        type_error l "only direct messages can have destination port"
    | None   -> () in
  check_msg_content_values msg.args mc sv

let check_send_internal (msg : msg_expr) (mc : typ_index IdMap.t)
                        (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_id with
    | Some _ ->
        type_error l
        ("messages to subfunctionalities cannot have " ^
         "destination port")
    | None -> () in
  check_msg_content_values msg.args mc sv

let is_msg_path_inb_inter_id_paths (mp : msg_path) (abip : basic_inter_path list) : bool = 
  let bpo = List.find_opt (fun bp -> fst bp = unlocs mp.inter_id_path) abip in
  match bpo with
  | Some _ -> true
  | None   -> false

let get_msg_def_for_msg_path (mp : msg_path) (bs : basic_inter_path list) :
                               message_def_body_tyd = 
  let iop = unlocs mp.inter_id_path in
  let bio = List.find (fun bp -> (fst bp) = iop) bs in
  let mt  =
    match mp.msg_or_other with
    | MsgPathId id -> unloc id
    | MsgPathOtherMsg _ ->
        failure "MsgPathOtherMsg doesn't have definition in interface" in
  let mdb = IdMap.find mt (snd bio) in
  unloc mdb

let check_send_msg_path (msg : msg_expr) (abip : all_basic_inter_paths)
                        (sv : state_vars) : msg_expr = 
  let ps = get_outgoing_msg_paths abip in
  let path' = check_msg_path ps msg.path in
  let msg' =
    {path = path'; args = msg.args;
     port_id = msg.port_id} in
  let () =
    if List.mem "simulator" sv.flags && msg.path <> msg'.path
    then type_error (msg_loc msg.path)
         ("messages sent by simulator must have complete path, did you mean " ^
          string_of_msg_path msg'.path ^ " ?")
    else () in
  msg'

let check_send (msg : msg_expr) (abip : all_basic_inter_paths)
               (sv : state_vars) : msg_expr = 
  let msg' = check_send_msg_path msg abip sv in
  let bs = abip.direct @ abip.adversarial @ abip.internal in
  let mdbc = (get_msg_def_for_msg_path msg'.path bs).params_map in
  let () =
    match msg'.path with
    | ( _ as p) when is_msg_path_inb_inter_id_paths p abip.direct ->
        check_send_direct msg' mdbc sv
    | ( _ as p) when is_msg_path_inb_inter_id_paths p abip.adversarial ->
        check_send_adversarial msg' mdbc sv
    | ( _ as p) when is_msg_path_inb_inter_id_paths p abip.internal ->
        check_send_internal msg' mdbc sv
    | _ ->
        failure
        ("impossible - the path is always in one of direct|" ^
         "adversarial|internal") in
  msg'

let check_send_and_transition (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                              (sat : send_and_transition) (sv : state_vars) :
                                instruction = 
  let msg' = check_send sat.msg_expr abip sv in
  let () = check_transition sat.state_expr ss sv in
  SendAndTransition {msg_expr = msg'; state_expr = sat.state_expr}

let merge_state_vars (sv1 : state_vars) (sv2 : state_vars) : state_vars = 
  {flags = sv1.flags; internal_ports = sv1.internal_ports;
   consts = sv1.consts; vars = sv1.vars;
   initialized_vs = IdSet.inter sv1.initialized_vs sv2.initialized_vs}

let rec check_ite (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                  (sv : state_vars) (ex : expression_l)
                  (tins : instruction_l list)
                  (eins : instruction_l list option) :
                    instruction*state_vars = 
  if check_expression sv ex <> bool_type
  then type_error (loc ex) "the condition must be a boolean expression"
  else let (tins_c, eins_c, sv') = check_branches abip ss sv tins eins in
       (ITE (ex, tins_c, eins_c), sv')

and check_branches (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                   (sv : state_vars) (tins : instruction_l list)
                   (eins : instruction_l list option) :
                     instruction_l list * instruction_l list option *
                     state_vars = 
  let (tins_c,tsv) = check_instructions abip ss sv tins in
  let (eins_c,esv) =
    match eins with                         
    | Some is ->
        let (is',esv) = check_instructions abip ss sv is in (Some is',esv)
    | None    -> (None, sv) in
  let sv' = merge_state_vars tsv esv in
  (tins_c, eins_c, sv')

and check_decode (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                 (sv : state_vars) (ex : expression_l) (ty : ty)
                 (m_is : pat list) (okins : instruction_l list)
                 (erins : instruction_l list) : instruction * state_vars = 
  if check_expression sv ex <> univ_type
  then type_error (loc ex) "only expressions of univ type can be decoded"
  else let dt =
         match check_type ty with
         | Tconstr (x, y) -> [Tconstr (x,y)]
         | Ttuple  t      -> t
         | _              ->
             failure
             ("check_type is supposed to return only " ^
              "Tconstr or Ttuple.") in
       if List.length m_is <> List.length dt
       then type_error (get_loc_match_item_list m_is)
            ("the number of bindings is different from the arity of " ^
             "decoded type")
       else let sv' = List.fold_left2 check_item_type_add_binding sv m_is dt in
            let (okins_c, erins_c, sv'') =
              check_branches abip ss sv' okins (Some erins) in
            ((Decode (ex, ty, m_is, okins_c, Option.get erins_c)), sv'')

and check_instruction (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                      (insv : instruction_l list * state_vars)
                      (i : instruction_l) : instruction_l list * state_vars = 
  let ins = fst insv in
  let sv = snd insv in
  match unloc i with
  | Assign (vid, ex)      -> (ins @ [i], check_val_assign sv vid ex)
  | Sample (vid, ex)      -> (ins @ [i], check_sampl_assign sv vid ex)
  | ITE (ex, tins, eins)  ->
      let (ite_c, sv') = check_ite abip ss sv ex tins eins in
      (ins @ [mk_loc (loc i) ite_c], sv')
  | Decode (ex, ty, m_is, okins, erins) ->
      let (match_c,sv') = check_decode abip ss sv ex ty m_is okins erins in
      (ins @ [mk_loc (loc i) match_c], sv')
  | SendAndTransition sat ->
      (ins @ [mk_loc (loc i) (check_send_and_transition abip ss sat sv)]), sv
  | Fail                  -> (ins @ [i], sv)

and check_instructions (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                       (sv : state_vars) (is : instruction_l list) :
                         (instruction_l list * state_vars) = 
  List.fold_left (check_instruction abip ss) ([],sv) is

let contains_sa_tor_f (is : instruction_l list) : bool = 
  List.exists
  (fun i ->
         match (unloc i) with
         | Fail                -> true
         | SendAndTransition _ -> true
         | _                   -> false)
  is

let rec check_ends_are_sa_tor_f (is : instruction_l list) : unit = 
  match is with
  | [] -> failure "the instruction list cannot be empty"
  | {pl_loc = _; pl_desc = (SendAndTransition _)} :: [] -> ()
  | {pl_loc = l; pl_desc = (SendAndTransition _)} :: _ :: _ ->
      type_error l
      ("the instructions after send and transition will " ^
       "not be executed")
  | {pl_loc = _; pl_desc = Fail} :: [] -> ()
  | {pl_loc = l; pl_desc = Fail} :: _ :: _ ->
      type_error l ("the instructions after fail will not be executed")
  | {pl_loc = _; pl_desc = (ITE (_,tins,Some eins))} :: [] ->
      (check_ends_are_sa_tor_f tins; check_ends_are_sa_tor_f eins)
  | {pl_loc = _; pl_desc = (ITE (_,tins,Some eins))} :: ins :: _
      when (contains_sa_tor_f tins)&&(contains_sa_tor_f eins) ->
      type_error (loc ins)
      ("the instructions after if-then-else will not be " ^
       " executed since both branches contain send and " ^
       "transition or fail commands")
  | {pl_loc = _; pl_desc = (Decode (_,_,_,okins,erins))} :: [] ->
      check_ends_are_sa_tor_f okins; check_ends_are_sa_tor_f erins
  | {pl_loc = _; pl_desc = (Decode (_,_,_,okins,erins))} :: ins :: _
      when contains_sa_tor_f okins && contains_sa_tor_f erins ->
      type_error (loc ins)
      ("the instructions after decode will not be executed " ^
       "since both branches contain send and transition or " ^
       "fail commands")
  | ins :: [] ->
      type_error (loc ins)
      ("every branch of execution must end with send and " ^
       "transition or fail command")
  | _ :: tl -> check_ends_are_sa_tor_f tl

let check_msg_code (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                   (sv : state_vars) (is : instruction_l list) :
                     instruction_l list = 
  let is_tyd = fst (check_instructions abip ss sv is) in
  let () = check_ends_are_sa_tor_f is_tyd in
  is_tyd

let check_message_path (abip : all_basic_inter_paths) (mmc : msg_match_clause) :
                         msg_match_clause = 
  let path' =
    check_msg_path (get_incoming_msg_paths abip) mmc.msg_pat.path in
  {msg_pat =
     {port_id = mmc.msg_pat.port_id;
      path = path'; pat_args = mmc.msg_pat.pat_args};
   code = mmc.code}

let check_m_mcode (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                  (sv : state_vars) (mmc : msg_match_clause) : msg_match_clause = 
  let mmc' = check_message_path abip mmc in 
  let sv' = check_match_bindings abip mmc'.msg_pat sv in
  let code' = check_msg_code abip ss sv' mmc'.code in
  {msg_pat = mmc'.msg_pat; code = code'}

let check_state_code (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                     (sv : state_vars) (mmclauses : msg_match_clause list) :
                       msg_match_clause list = 
  let mmclauses' = List.map (fun mmc -> check_m_mcode abip ss sv mmc) mmclauses in
  let () =
    check_msg_match_deltas abip
    (List.map (fun mmc -> mmc.msg_pat) mmclauses') in
  mmclauses'

let get_keys (m : 'a IdMap.t) : QidSet.t = 
  let lp = fst(List.split (IdMap.bindings m)) in
  List.fold_left (fun s p -> QidSet.add [p] s) QidSet.empty lp

let get_internal_ports (r_f : fun_body_tyd) : QidSet.t = 
  QidSet.union
  (get_keys (parties_of_fun_body_tyd r_f))
  (QidSet.union (get_keys (params_of_fun_body_tyd r_f))
                (get_keys (sub_funs_of_fun_body_tyd r_f)))

let filterb_inter_id_paths (abip : basic_inter_path list) (pfxs : string list located list) :
                       basic_inter_path list = 
  List.filter
  (fun bp -> List.exists (fun pfx -> unloc pfx = fst bp) pfxs)
  abip

let get_fb_inter_id_paths (dir_inter_map : inter_tyd IdMap.t)
                          (adv_inter_map : inter_tyd IdMap.t)
                          (f : fun_tyd) : all_basic_inter_paths = 
  let uf = unloc f in
  let iddir = id_dir_inter_of_fun_body_tyd uf in
  let direct = get_basic_inter_paths_from_inter_id iddir dir_inter_map in
  let adversarial = 
    match id_adv_inter_of_fun_body_tyd uf with
    | Some id -> get_basic_inter_paths_from_inter_id id adv_inter_map
    | None -> [] in
  {direct = direct; adversarial = adversarial; internal = []}

let get_all_basic_inter_paths (dir_inter_map : inter_tyd IdMap.t)
                      (adv_inter_map : inter_tyd IdMap.t)
                      (funs : fun_tyd IdMap.t) (r_f : fun_tyd)
                      (p : party_def_tyd) : all_basic_inter_paths = 
  let all = get_fb_inter_id_paths dir_inter_map adv_inter_map r_f in
  let ur_f = unloc r_f in
  let filt = (unloc p).serves in
  let direct =  filterb_inter_id_paths all.direct filt in
  let adversarial = filterb_inter_id_paths all.adversarial filt in
  let internal_sfm =
    IdMap.mapi
    (fun sfid (sf : id) ->
           let did = get_dir_inter_id_impl_by_fun (unloc sf) funs in
           get_basic_inter_paths sfid did dir_inter_map)
    (sub_funs_of_fun_body_tyd ur_f) in
  let internal_pm =
    IdMap.mapi
    (fun pid p -> 
           let did = unloc (fst p) in
           get_basic_inter_paths pid did dir_inter_map)
    (params_of_fun_body_tyd ur_f) in
  let internal_m =
    IdMap.union
    (fun _ _ _ ->
       failure
       ("Impossible, we already checked params and " ^
        "subfuns have different ids"))
    internal_sfm internal_pm in
  let internal = IdMap.fold (fun _ abip l -> l @ abip) internal_m [] in
  {direct = direct; adversarial = adversarial; internal = internal}

let check_state (ur_f : fun_body_tyd) (states : state_tyd IdMap.t)
                (abip : all_basic_inter_paths) (s : state_tyd) : state_tyd = 
  let us = unloc s in
  let sv = init_state_vars (unloc s) (get_internal_ports ur_f) [] in
  let ss = get_state_sigs states in
  let mmclauses' = check_state_code abip ss sv us.mmclauses in
  mk_loc (loc s)
         {is_initial = us.is_initial; params = us.params; vars = us.vars;
          mmclauses = mmclauses'}

let check_fun (maps : maps_tyd) (fund : fun_def) : maps_tyd =
  let uid = unloc fund.id in
  let () =
    if exists_id_maps_tyd maps uid
    then type_error (loc fund.id)
         ("identifier already declared at top-level: " ^ uid) in
  let () = check_exists_inter DirectInterKind maps.dir_inter_map fund.id_dir in
  let () = check_is_composite DirectInterKind  maps.dir_inter_map fund.id_dir in
  let uid_dir_inter = unloc fund.id_dir in 
  let uid_adv_inter =
    match fund.id_adv with
    | None    -> None
    | Some id -> 
        (check_exists_inter AdversarialInterKind maps.adv_inter_map id;
         Some(unloc id)) in
  match fund.fun_body with
  | FunBodyReal fbr ->
      let () =
        match fund.id_adv with
        | None    -> ()
        | Some id ->
            check_is_composite AdversarialInterKind maps.adv_inter_map id in
      let params = check_real_fun_params maps.dir_inter_map fund.params in 
      let sub_fun_decls =
        check_unique_ids "duplicate subfunctionality name: "
        fbr.sub_fun_decls (fun x -> x.id) in
      let () =
        let dup_ids =
          IdMap.filter (fun id _ -> IdMap.mem id params) sub_fun_decls in
        if IdMap.is_empty dup_ids then ()
        else let id, dup = IdMap.choose dup_ids in
             type_error (loc dup.id)
             ("the name " ^ id ^
              " is the same name as one of the functionality's parameters") in
      let check_sub_fun_decl (sf : sub_fun_decl) : id =
        let fun_id = unloc sf.fun_id in
        match IdMap.find_opt fun_id maps.fun_map with
        | None    ->
            type_error (loc sf.fun_id)
            ("nonexisting functionality: " ^ fun_id)
        | Some ft ->
            let fbt = unloc ft in
            if is_real_fun_body_tyd fbt
            then type_error (loc sf.fun_id)
                 (fun_id ^ " is not an ideal functionality")
            else mk_loc (loc sf.id) fun_id in
      let sub_funs = IdMap.map check_sub_fun_decl sub_fun_decls in
      let party_defs =
        check_unique_ids "duplicate party name: " fbr.party_defs
        (fun x -> x.id) in
      let parties =
        let ps =
          IdMap.map
          (check_toplevel_party_def uid_dir_inter uid_adv_inter
           maps.dir_inter_map maps.adv_inter_map)
          party_defs in
        (check_parties_serve_distinct_cover ps uid_dir_inter uid_adv_inter
         maps.dir_inter_map maps.adv_inter_map;
         ps) in
      let ft =
        mk_loc (loc fund.id)
        (FunBodyRealTyd
         {params = params; id_dir_inter = uid_dir_inter;
          id_adv_inter = uid_adv_inter; sub_funs = sub_funs;
          parties = parties}) in
      let parties' =
        IdMap.map 
        (fun p -> 
           let up = unloc p in
           let abip =
             get_all_basic_inter_paths
             maps.dir_inter_map maps.adv_inter_map maps.fun_map ft p in
           let states = up.states in
           let states' =
             IdMap.map (check_state (unloc ft) states abip) states  in
           mk_loc (loc p) {serves = up.serves; states = states'})
        parties in
      {maps with
         fun_map =
           IdMap.add uid
           (mk_loc (loc fund.id)
            (FunBodyRealTyd
             {params = params; id_dir_inter = uid_dir_inter;
              id_adv_inter = uid_adv_inter; sub_funs = sub_funs;
              parties = parties'}))
           maps.fun_map}
  | FunBodyIdeal state_defs ->
      let states =
        match fund.id_adv with
        | None ->
            type_error (loc fund.id)
            ("an ideal functionality must implement a basic adversarial " ^
             "interface")
        | Some id ->
            (check_exists_inter AdversarialInterKind maps.adv_inter_map id;
             check_is_basic AdversarialInterKind maps.adv_inter_map id;
             check_toplevel_states fund.id state_defs) in
      let ifbt =
        {id_dir_inter = uid_dir_inter; id_adv_inter = Option.get uid_adv_inter;
         states = states} in
      let ft = mk_loc (loc fund.id) (FunBodyIdealTyd ifbt) in
      let states' =
        let states = ifbt.states in
        let abip =
          get_fb_inter_id_paths maps.dir_inter_map maps.adv_inter_map
          ft in
        IdMap.map (check_state (unloc ft) states abip) states in
      {maps with
         fun_map =
           IdMap.add uid
           (mk_loc (loc fund.id)
            (FunBodyIdealTyd
             {id_dir_inter = uid_dir_inter;
              id_adv_inter = Option.get uid_adv_inter;
              states = states'}))
           maps.fun_map}

(****************************** simulator checks ******************************)

let check_msg_code_sim (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
                       (mmc : msg_match_clause) (sv : state_vars) :
                         msg_match_clause = 
  let code' = check_msg_code abip ss sv mmc.code in
  {msg_pat = mmc.msg_pat; code = code'}

let check_message_path_sim (abip : basic_inter_path list) (isini : bool)
                           (mmc : msg_match_clause) : unit = 
  let abip = filter_dir_basic_inter_paths In abip in
  let mp = mmc.msg_pat.path in
  let l = msg_loc mp in
  let id = fst (List.find (fun p -> (List.length (fst p)) = 1) abip) in
  if isini && unlocs mp.inter_id_path <> id
  then type_error l
       ("initial state can handle only messages comming " ^
        "from ideal functionality. did you omit prefix " ^
        List.hd id ^ ".?")
  else let iops = fst (List.split abip) in
       let invalid_dest () =
         type_error l
         ("not a valid destination, these destinations are " ^
          "valid: " ^ string_of_id_paths iops) in
       let umpiop = (unlocs mp.inter_id_path) in
       match mp.msg_or_other with
       | MsgPathId mt ->
           if not(List.mem umpiop iops)
             then invalid_dest ()
           else if List.exists
                   (fun bp ->
                          fst bp = umpiop &&
                          IdMap.mem (unloc mt) (snd bp))
                   abip
             then ()
           else type_error (loc mt)
                (unloc mt ^ " is not an incoming message of " ^
                 string_of_id_path umpiop)
       | MsgPathOtherMsg _ ->
           if List.exists
              (fun p -> sl1_starts_with_sl2 p umpiop)
              iops
           then ()
           else invalid_dest ()

let check_match_bindings_sim (abip : basic_inter_path list) (sv : state_vars)
                             (mmc : msg_match_clause) : state_vars = 
  let mm = mmc.msg_pat in
  check_pat_args abip mm sv

let check_msg_match_deltas_sim (abip : all_basic_inter_paths)
                               (mmclauses : msg_match_clause list) : unit = 
  let mps = get_incoming_msg_paths abip in
  ignore
  (check_mm_ds_non_empty mps
   (List.map
    (fun mmc ->
          {inter_id_path = mmc.msg_pat.path.inter_id_path;
           msg_or_other = mmc.msg_pat.path.msg_or_other})
    mmclauses))

let check_sim_state_code (bips : basic_inter_path list) (ss : state_sig IdMap.t)
                         (sv : state_vars) (isini : bool)
                         (mmclauses : msg_match_clause list) :
                           msg_match_clause list = 
  let () = List.iter (check_message_path_sim bips isini) mmclauses in
  let svs = List.map (check_match_bindings_sim bips sv) mmclauses in
  let abip = {direct = []; adversarial = bips; internal = []} in
  let ret = List.map2 (check_msg_code_sim abip ss) mmclauses svs in
  let () = check_msg_match_deltas_sim abip ret in
  ret

(* TODO : fix this *)
let disj (_ : 'key) (_ : 'a) (_ : 'a) = 
  failure "Not disjoint!"

let disj_union (qml : 'a QidMap.t list) : 'a QidMap.t = 
  List.fold_left (fun qm1 qm2 -> QidMap.union disj qm1 qm2) QidMap.empty qml

let get_sim_components (funs : fun_tyd IdMap.t) (r_f : string)
                       (ps : string list) : fun_body_tyd QidMap.t = 
  let rec get_sc (funs : fun_tyd IdMap.t) (fid : string) (pfx : SL.t) :
                   fun_body_tyd QidMap.t = 
    if IdMap.mem fid funs
    then let urf = unloc(IdMap.find fid funs) in
         disj_union
         (QidMap.singleton pfx (urf) ::
          IdMap.fold
          (fun sfid sfd l ->
                 (get_sc funs (unloc sfd) (pfx @ [sfid])) :: l)
          (sub_funs_of_fun_body_tyd urf) [])
    else failure
         ("Impossible! We already checked that all referenced " ^
          "functionalities exist") in
  let urf = unloc(IdMap.find r_f funs) in
  let pids =
    IdMap.fold (fun pid _ l -> pid :: l) (params_of_fun_body_tyd urf) [] in
  let qpids = List.map (fun pid -> r_f :: [pid]) pids in
  disj_union(get_sc funs r_f [r_f] :: List.map2 (get_sc funs) ps qpids)
                
let get_component_inter_id_paths (adv_inter_map : inter_tyd IdMap.t)
                                 (f : fun_body_tyd) : basic_inter_path list = 
  match id_adv_inter_of_fun_body_tyd f with
  | Some id -> get_basic_inter_paths_from_inter_id id adv_inter_map 
  | None    -> []

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In

let invert_mdf (mdf : message_def_body_tyd) : message_def_body_tyd = 
  {dir = (invert_dir mdf.dir);
   params_map = mdf.params_map; port = mdf.port}

let invert_md_fl (mdfl : message_def_body_tyd located) :
      message_def_body_tyd located = 
  let l = loc mdfl in
  let mdf = unloc mdfl in
  let mdf' = invert_mdf mdf in
  mk_loc l mdf'

let invertb_i_ob_tyd (bio : basic_inter_body_tyd) : basic_inter_body_tyd = 
  IdMap.map invert_md_fl bio

let invert_msg_dirs (bp : basic_inter_path) : basic_inter_path = 
  let bio = snd bp in
  let bio' = invertb_i_ob_tyd bio in
  (fst bp, bio')

let get_simb_inter_id_paths (adv_inter_map : inter_tyd IdMap.t) (uses : string)
                      (cs : fun_body_tyd QidMap.t) : basic_inter_path list = 
  let sbps = QidMap.map (get_component_inter_id_paths adv_inter_map) cs in        
  let bps =
    QidMap.add
    []
    (List.map
     (fun bp -> invert_msg_dirs bp)
     (get_basic_inter_paths_from_inter_id uses adv_inter_map))
    sbps in
  QidMap.fold
  (fun q bpl l ->
         l @ List.map (fun bp -> (q @ fst bp, snd bp)) bpl)
  bps []

let get_sim_internal_ports (cs : fun_body_tyd QidMap.t) : QidSet.t = 
  let rcsips = QidMap.map (fun fb -> get_internal_ports fb) cs in
  let rcsqips =
    QidMap.mapi (fun q ips -> QidSet.map (fun ip -> q@ip) ips) rcsips in
  QidMap.fold (fun _ qips sip -> QidSet.union qips sip) rcsqips QidSet.empty
        
let check_sim_code (_ : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
                   (funs : fun_tyd IdMap.t) (sim : sim_def_tyd) : sim_def_tyd = 
  let usim = unloc sim in
  let states = usim.states in
  let ss = get_state_sigs states in
  let cs = get_sim_components funs usim.sims usim.sims_arg_ids in
  let bps = get_simb_inter_id_paths adv_inter_map usim.uses cs in
  let states' =
    IdMap.map 
    (fun s -> 
           let us = unloc s in
           let sv =
             init_state_vars us (get_sim_internal_ports cs) ["simulator"] in
           let mmclauses' =
             check_sim_state_code bps ss sv us.is_initial us.mmclauses in
           mk_loc (loc s)
                  {is_initial = us.is_initial; params = us.params;
                   vars = us.vars; mmclauses = mmclauses'})
    states in
  mk_loc (loc sim)
         {uses = usim.uses; sims = usim.sims;
          sims_arg_ids = usim.sims_arg_ids; states = states'}

let check_exists_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let urf = unloc rf in
  if exists_id funs urf then ()
  else type_error (loc rf) ("functionality isn't defined: " ^ urf)

let check_is_real_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let () = check_exists_f funs rf in
  let f = unloc (IdMap.find (unloc rf) funs) in
  if not (is_real_fun_body_tyd f)
  then type_error (loc rf)
       ("the simulated functionality must be a real functionality")

let check_sim_fun_params (funs : fun_tyd IdMap.t) (_ : inter_tyd IdMap.t)
                         (rf : id) (params : id list) = 
  let d_ios = get_param_dir_inter_ids funs (unloc rf) in
  let d_ios' =
    List.map
    (fun id -> get_dir_inter_id_impl_by_fun id funs) (unlocs params) in
  if List.length d_ios <> List.length d_ios'
  then type_error (loc rf)
       ("wrong number of arguments for functionality")
  else let () =
         List.iteri
         (fun i pid ->
          if List.nth d_ios i <> List.nth d_ios' i
          then type_error (loc pid)
               ("argument implements different direct interface than " ^
                "required by functionality"))
         params in
       List.iter
       (fun pid ->
              let f = unloc (IdMap.find (unloc pid) funs) in
              match f with
              | FunBodyRealTyd _ ->
                  type_error (loc pid)
                  ("the argument to simulated functionality must " ^
                   "be an ideal functionality")
              | FunBodyIdealTyd _  ->
                  (* we know the ideal functionality implements a basic
                     adversarial interface *)
                  ())
       params

let check_sim_decl (adv_inter_map : inter_tyd IdMap.t)
                   (fun_map : fun_tyd IdMap.t) (sd : sim_def) : sim_def_tyd = 
  let () = check_exists_inter AdversarialInterKind adv_inter_map sd.uses in
  let () = check_is_basic AdversarialInterKind adv_inter_map sd.uses in
  let uses = unloc sd.uses in
  let () = check_is_real_f fun_map sd.sims in
  let sims = unloc sd.sims in
  let () = List.iter (check_exists_f fun_map) sd.sims_arg_ids in
  let () = check_sim_fun_params fun_map adv_inter_map sd.sims sd.sims_arg_ids in
  let sims_param_ids = unlocs sd.sims_arg_ids in
  let body = check_toplevel_states sd.id sd.states in
  mk_loc (loc sd.id)
  {uses = uses; sims = sims; sims_arg_ids = sims_param_ids; states = body}

let check_sim (maps : maps_tyd) (simd : sim_def) : maps_tyd =
  let uid = unloc simd.id in
  let () =
    if exists_id_maps_tyd maps uid
    then type_error (loc simd.id)
         ("identifier already declared at top-level: " ^ uid) in
  let sdt =
    check_sim_decl maps.adv_inter_map maps.fun_map simd in
  let sdt =
    check_sim_code maps.dir_inter_map maps.adv_inter_map maps.fun_map sdt in
  {maps with sim_map = IdMap.add uid sdt maps.sim_map}

(***************************** definition checks ******************************)

let check_defs defs = 
  let empty_maps =
    {dir_inter_map = IdMap.empty;
     adv_inter_map = IdMap.empty;
     fun_map       = IdMap.empty;
     sim_map       = IdMap.empty} in
  let check_def maps def =
    match def with
    | InterDef interd -> check_inter_def maps interd
    | FunDef fund     -> check_fun maps fund
    | SimDef simd     -> check_sim maps simd in
  let maps = List.fold_left check_def empty_maps defs in
  {direct_inters      = maps.dir_inter_map;
   adversarial_inters = maps.adv_inter_map;
   functionalities    = maps.fun_map;
   simulators         = maps.sim_map }

(**************************** specification checks ****************************)

let load_ec_reqs reqs = 
  let reqimp id = 
    let uid = unloc id in
    let () =
      if not (Char.is_uppercase uid.[0])
      then type_error (loc id)
           ("EasyCrypt theory to be imported must begin with uppercase " ^
            "letter: " ^ uid) in
    try UcEcInterface.require_import (unloc id) with
    Failure f ->
      type_error (loc id)
      ("error when importing EasyCrypt theory " ^ unloc id ^ ":\n" ^ f) in
  List.iter reqimp reqs

let typecheck spec = 
  let () = UcEcInterface.init() in
  let () = load_ec_reqs spec.externals.ec_requires in
  check_defs spec.definitions
