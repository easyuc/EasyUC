(* UcTypecheck module *)

(* Typecheck a specification *)

open Batteries
open Format
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

let exists_id_inter_maps
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (uid : string) : bool =
  exists_id dir_inter_map uid || exists_id adv_inter_map uid

(* convert a named list into an id map, checking for uniqueness
   of names; get_id returns the name of a list element *)

let check_unique_ids
    (msgf : formatter -> unit) (al : 'a list) (get_id : 'a -> id)
      : 'a IdMap.t = 
  let id_map = IdMap.empty in
  List.fold_left 
  (fun id_map a -> 
     let id_l = get_id a in 
     if exists_id id_map (unloc id_l) then 
       type_error (loc id_l)
       (fun ppf -> fprintf ppf "@[%t:@ %s@]" msgf (unloc id_l))
     else IdMap.add (unloc id_l) a id_map)
  id_map al

(* EasyCrypt type checks *)

let check_name_type_bindings
    (msgf : formatter -> unit) (ntl : type_binding list)
      : typ_index IdMap.t = 
  let nt_map = check_unique_ids msgf ntl (fun nt -> nt.id) in
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
      (fun ppf ->
         fprintf ppf
         "@[%s isn't %s interface name@]" uid (inter_kind_to_str true ik))
  | Some it ->
      let ibt = unloc it in
      if is_composite_tyd ibt
      then type_error (loc ci.inter_id)
           (fun ppf ->
              fprintf ppf
              "@[%s isn't a basic interface@]" uid)
      else mk_loc (loc ci.sub_id) (unloc ci.inter_id)

let check_basic_inter (mds : message_def list) : inter_body_tyd = 
  let msg_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ message@ name@]")
    mds (fun md -> md.id) in
  BasicTyd
  (IdMap.map
   (fun (md : message_def) ->
      mk_loc
      (loc md.id)
      {dir = md.dir;
       params_map =
         check_name_type_bindings
         (fun ppf -> fprintf ppf "@[duplicate message parameter name:@]")
         md.params;
       port = md.port})
  msg_map)

let check_comp_inter (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                     (cis : comp_item list) : inter_body_tyd = 
  let comp_item_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ sub-interface@ name@]")
    cis (fun ci -> ci.sub_id) in
  CompositeTyd (IdMap.map (check_comp_item ik inter_map) comp_item_map)

let check_inter
    (e_maps : string -> bool) (ik : inter_kind)
    (inter_map : inter_tyd IdMap.t) (ni : named_inter) = 
  let uid = unloc ni.id in
  let () =
    if e_maps uid
    then type_error (loc ni.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at top-level:@ %s@]" uid) in
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

let check_exists_inter
    (ik : inter_kind) (inter_map : inter_tyd IdMap.t) (id : id) : unit = 
  let uid = unloc id in
  if exists_id inter_map uid then () 
  else type_error (loc id)
       (fun ppf ->
          fprintf ppf
          "@[%s interface does not exist: %s@]"
          (inter_kind_to_str false ik) uid)

(* the following two functions assume id exists in inter_map *)

let check_is_basic (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
                   (id : id) : unit = 
  let uid = unloc id in
  match unloc (IdMap.find uid inter_map) with
  | BasicTyd _     -> ()
  | CompositeTyd _ ->
      type_error (loc id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ interface@ must@ be@ basic:@ %s@]"
         (inter_kind_to_str false ik) uid)

let check_is_composite
    (ik : inter_kind) (inter_map : inter_tyd IdMap.t) (id : id) : unit = 
  let uid = unloc id in
  match unloc (IdMap.find uid inter_map) with
  | BasicTyd _     ->
      type_error (loc id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ interface@ must@ be@ composite:@ %s@]"
         (inter_kind_to_str false ik) uid)
  | CompositeTyd _ -> ()

(************************* real functionality checks **************************)

(* functionality parameter checking *)

let check_real_fun_params
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (params : fun_param list) : (id * int) IdMap.t = 
  let check_real_fun_param (param : fun_param) : id * int = 
    let () = check_exists_inter DirectInterKind dir_inter_map param.id_dir in
    let () = check_is_composite DirectInterKind dir_inter_map param.id_dir in
    let () =
      if exists_id_inter_maps dir_inter_map adv_inter_map (unloc param.id)
      then type_error (loc param.id)
           (fun ppf ->
              fprintf ppf
              ("@[functionality@ parameter@ name@ may@ not@ be@ same@ " ^^
               "as@ top-level@ interface@ name@]")) in
     (mk_loc (loc param.id) (unloc param.id_dir),
      index_of_ex param params) in
  let param_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ functionality@ parameter@ name@]")
    params (fun p -> p.id) in
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
  | 0 ->
      type_error (loc id)
      (fun ppf ->
         fprintf ppf "@[%s@ doesn't@ have@ initial@ state@]" (unloc id))
  | 1 ->
      (match List.hd inits with
       | InitialState s   -> s.id
       | FollowingState _ ->
           failure "impossible, list contains only InitialState")
  | _ ->
      type_error (loc id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ has@ more@ than@ one@ initial@ state@]" (unloc id))
let check_toplevel_state (init_id : id) (st : state) : state_tyd = 
  let is_initial = (init_id = st.id) in
  let params =
    check_name_type_bindings
    (fun ppf -> fprintf ppf "@[duplicate@ parameter@ name@]")
    (unloc st.params) in
  let vars =
    IdMap.map
    (fun ti -> mk_loc (loc ti) (fst (unloc ti)))
    (check_name_type_bindings
     (fun ppf -> fprintf ppf "@[duplicate@ variable@ name@]")
     st.code.vars) in
  let dup = IdMap.find_first_opt (fun uid -> IdMap.mem uid params) vars in
  match dup with
  | None        ->
      mk_loc (loc st.id)
      {is_initial = is_initial; params = params; vars = vars;
       mmclauses = st.code.mmclauses}
  | Some (uid, typ) ->
      type_error (loc typ)
      (fun ppf ->
         fprintf ppf
         ("@[variable@ name@ %s@ is@ the@ same@ as@ one@ of@ the@ " ^^
          "state's@ parameters@]")
         uid)
                        
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
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ state@ name@]")
    states (fun s -> s.id) in
  IdMap.map (check_toplevel_state init_id) state_map 

(* a basic_inter_path will have the form (ids, b) where

   *** for functionalities ***

   ids = [id2], and id2 is the name of an adversarial basic interface,
   and b is that basic interface (possibly filtered to have only
   incoming or outgoing messages); or

   ids = [id1; id2], and id1 is the name of a composite interface, id2
   is the name of one of that composite interface's sub-interfaces,
   and b is the basic interface (direct iff the composite interface is
   direct) corresponding to the interface name that id2 is associated
   with in the composite interface (possibly filtered to have only
   incoming or outgoing messages); or

   ids = [id1; id2], and id1 is the name of a parameter or
   subfunctionality of a real functionality, id2 is the name of one of
   the sub-interfaces of the composite direct interface implemented by
   the parameter or subfunctionality (in the case of a
   subfunctionality, the direct interface implemented by the ideal
   functionality the subfunctionality is an instance of), and b is the
   basic, direct interface corresponding to the interface name that
   id2 is associated with in the composite interface (possibly
   filtered to have only incoming or outgoing messages)

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

type basic_inter_path = string list * basic_inter_body_tyd

(* three kinds of basic_inter_path's - ones of a direct interface,
   ones of an adversarial interface, and internal ones (coming from a
   real functionality's subfunctionalities' direct interfaces) *)

type all_basic_inter_paths =
  {direct : basic_inter_path list; adversarial : basic_inter_path list;
   internal : basic_inter_path list}

let flatten_all_basic_inter_paths (abip : all_basic_inter_paths)
      : basic_inter_path list = 
  abip.direct @ abip.adversarial @ abip.internal

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
    (msgf : formatter -> unit) (idps : string list located list) : unit = 
  ignore
  (List.fold_left
   (fun l idp -> 
      let uidp = unloc idp in
      if List.mem uidp l
      then type_error (loc idp) msgf
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
  else type_error loc
       (fun ppf ->
          fprintf ppf
          ("@[%s@ is@ not@ the@ path@ of@ a@ component@ of@ an@ interface@ " ^^
           "implemented@ by@ functionality@]")
          (string_of_id_path uidp))

let check_served_paths
    (serves : string list located list)
    (id_dir_inter : string) (party_id : id) : unit = 
  let er ppf =
    fprintf ppf
    ("@[a@ party@ must@ serve@ one@ basic@ direct@ interface,@ and@ may " ^^
     "optionally@ serve@ one@ basic@ adversarial@ interface@]") in
  let erone ppf =
    fprintf ppf
    "@[a@ party@ must@ serve@ one@ basic@ direct@ interface@]" in
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
  else type_error (mergelocs served_ps)
       (fun ppf ->
          fprintf ppf
          ("@[these@ sub-interfaces@ are@ not@ served@ by@ any@ " ^^
           "party:@;<1 2>%a@]")
          format_id_paths_comma unserved)

let check_parties_serve_distinct_cover
    (parties : party_def_tyd IdMap.t)
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
      : unit = 
  let served_ps =
    IdMap.fold (fun _ p l -> l @ (unloc p).serves) parties [] in
  let () =
    check_id_paths_unique
    (fun ppf ->
       fprintf ppf
       "@[parties@ must@ serve@ distinct@ sub-interfaces@]")
    served_ps in
  check_id_paths_cover id_dir_inter id_adv_inter
  dir_inter_map adv_inter_map served_ps

let get_dir_inter_id_impl_by_fun_id
    (funid : string) (fun_map : fun_tyd IdMap.t) : string = 
  let func = IdMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr  -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

let get_params_of_real_fun_id
    (fun_map : fun_tyd IdMap.t) (funid : string) : string list = 
  let func = IdMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr -> unlocs (indexed_map_to_list fbr.params)
  | FunBodyIdealTyd _  -> failure "cannot happen - will be real functionality"

let string_of_msg_path (mp : msg_path) : string = 
  let siop = string_of_id_path (unlocs mp.inter_id_path) in
  if siop = ""
  then unloc mp.msg
  else siop ^ "." ^ unloc mp.msg

let string_of_msg_path_pat (mpp : msg_path_pat) : string = 
  let siop = string_of_id_path (unlocs mpp.inter_id_path) in
  let msg_or_star =
    match mpp.msg_or_star with 
    | MsgOrStarMsg id -> unloc id
    | MsgOrStarStar _ -> "*" in
  if siop = "" then msg_or_star else siop ^ "." ^ msg_or_star

let format_msg_path_list
    (ppf : formatter) (mps : msg_path list) : unit =
  format_strings_comma ppf (List.map string_of_msg_path mps)

let filter_dir_basic_inter_paths
    (dir : msg_dir) (bips : basic_inter_path list) : basic_inter_path list = 
  List.map
  (fun bip ->
     (fst bip,
      IdMap.filter
      (fun _ md -> (unloc md).dir = dir)
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

let msg_path_loc (mp : msg_path) : EcLocation.t = 
  let ml = loc mp.msg in
  if List.is_empty mp.inter_id_path
  then ml
  else merge (mergelocs mp.inter_id_path) ml

let msg_path_pat_loc (mpp : msg_path_pat) : EcLocation.t = 
  let ml =
    match mpp.msg_or_star with
    | MsgOrStarMsg id -> loc id
    | MsgOrStarStar l -> l in
  if List.is_empty mpp.inter_id_path
  then ml
  else merge (mergelocs mpp.inter_id_path) ml

let msg_paths_of_basic_inter_path (bp : basic_inter_path) : msg_path list =   
  IdMap.fold
  (fun id _ l ->
     {inter_id_path = dummylocl (fst bp);
      msg           = dummyloc id} :: l)
  (snd bp) []

let msg_paths_of_basic_inter_paths
    (bpl : basic_inter_path list) : msg_path list = 
  List.flatten (List.map (fun bp -> msg_paths_of_basic_inter_path bp) bpl)

let msg_paths_of_all_basic_inter_paths (abip : all_basic_inter_paths)
      : msg_path list = 
  msg_paths_of_basic_inter_paths (flatten_all_basic_inter_paths abip)

let check_outgoing_msg_path
    (abip : all_basic_inter_paths) (mp : msg_path) : unit = 
  let allps = msg_paths_of_all_basic_inter_paths abip in       
  if List.exists
     (fun p -> string_of_msg_path p = string_of_msg_path mp)
     allps
  then ()
  else type_error (msg_path_loc mp)
       (fun ppf ->
          fprintf ppf
          ("@[message@ path@ is@ not@ one@ of@ the@ possible@ outgoing@ " ^^
           "messages:@;<1 2>%a@]")
       format_msg_path_list allps)

let check_msg_path_pat
    (abip : all_basic_inter_paths) (mpp : msg_path_pat) : unit = 
  let allps = msg_paths_of_all_basic_inter_paths abip in       
  match mpp.msg_or_star with
  | MsgOrStarMsg _      -> 
      if List.exists
         (fun p -> string_of_msg_path p = string_of_msg_path_pat mpp)
         allps
      then ()
      else type_error (msg_path_pat_loc mpp)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ is@ not@ one@ of@ the@ possible@ " ^^
               "incoming@ messages:@;<1 2>%a@]")
              format_msg_path_list allps)
  | MsgOrStarStar _ ->
      if (List.exists
          (fun p -> qid1_starts_with_qid2 p.inter_id_path mpp.inter_id_path)
          allps)
      then ()
      else type_error (msg_path_pat_loc mpp)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ pattern@ is@ inconsistent@ with@ the@ " ^^
               "paths@ of@ possible@ incoming@ messages:@;<1 2>%a@]")
               format_msg_path_list allps)

let remove_covered_paths (mps : msg_path list) (mpp : msg_path_pat)
      : msg_path list = 
  let covered mp1 mpp2 = 
    match mpp2.msg_or_star with
    | MsgOrStarMsg _  ->
        string_of_msg_path mp1 = string_of_msg_path_pat mpp2
    | MsgOrStarStar _ ->
        qid1_starts_with_qid2 mp1.inter_id_path mpp2.inter_id_path in
  let rem = List.filter (fun mp' -> not (covered mp' mpp)) mps in
  if List.length mps = List.length rem
  then type_error (msg_path_pat_loc mpp)
       (fun ppf ->
          fprintf ppf
          ("@[this@ pattern@ is@ covered@ by@ previous@ patterns@ and@ " ^^
           "would@ never@ match@]"))
  else rem

let msg_match_deltas
    (abip : all_basic_inter_paths) (mppl : msg_path_pat list)
      : msg_path list = 
  let mps = msg_paths_of_all_basic_inter_paths abip in
  List.fold_left (fun mps mp -> remove_covered_paths mps mp) mps mppl

let check_msg_match_deltas
    (abip : all_basic_inter_paths) (mml : msg_pat list) : unit = 
  let mps = incoming_abip abip in
  let r =
    msg_match_deltas mps
    (List.map (fun (mm : msg_pat) -> mm.msg_path_pat) mml) in
  if r <> []
  then let l = msg_path_pat_loc (List.last mml).msg_path_pat in
       type_error l
       (fun ppf ->
          fprintf ppf
          ("@[message@ patterns@ are@ not@ exhaustive;@ these@ " ^^
           "messages@ are@ not@ matched:@;<1 2>%a@]")
          format_msg_path_list r)

type state_info =
  {flags : string list;
   internal_ports : QidSet.t;
   consts : typ IdMap.t;
   vars : typ IdMap.t;
   initialized_vs : IdSet.t}

let init_state_info
    (s : state_body_tyd) (ports : QidSet.t)
    (flags : string list) : state_info = 
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

let get_declared (si : state_info) = 
  IdMap.union
  (fun _ _ _ ->
     failure
     ("@[impossible, we already checked params and local " ^
      "vars have different ids@]"))
  si.consts si.vars

let check_declared_with_compatible_type
    (id : id) (typ : typ) (si : state_info) : unit = 
  let uid = unloc id in
  let decs = get_declared si in
  if not (IdMap.mem uid decs)
  then type_error (loc id)
       (fun ppf -> fprintf ppf "@[%s@ is@ not@ declared@]" uid)
  else let idt = IdMap.find uid decs in
       if not (compatible_types idt typ)
       then type_error (loc id)
            (fun ppf ->
               fprintf ppf
               "@[type@ %a@ of@ %s@ is@ not@ compatible@ with@ type@ %a@]"
               format_typ idt (unloc id) format_typ typ)

let check_assign_core
    (vid : id) (typ : typ) (si : state_info) : state_info = 
  let uvid = unloc vid in
  if not (IdMap.mem uvid si.vars)
  then type_error (loc vid)
       (fun ppf -> fprintf ppf ("@[%s@ is@ not@ a@ declared variable@]") uvid)
  else (check_declared_with_compatible_type vid typ si;
        {si with
           initialized_vs = IdSet.add uvid si.initialized_vs})

let check_add_const
    (cid : id) (ct : typ) (si : state_info) : state_info = 
  let ucid = unloc cid in
  let pvs = get_declared si in
  if IdMap.mem ucid pvs
  then type_error (loc cid)
       (fun ppf ->
          fprintf ppf
          ("@[pattern@ variable@ already@ bound@ as@ parameter,@ " ^^
           "variable@ or pattern@ variable:@ %s@]")
          ucid)
  else {flags = si.flags; internal_ports = si.internal_ports;
        consts = IdMap.add ucid ct si.consts; vars = si.vars;
        initialized_vs = si.initialized_vs}

let check_port_var_binding
    (abip : all_basic_inter_paths) (mp : string list)
    (vid : id) (si : state_info) : state_info = 
  let d = List.exists (fun bp -> fst bp = mp) abip.direct in
  let is_sim = List.mem "simulator" si.flags in
  if not d
  then type_error (loc vid)
       (fun ppf ->
          fprintf ppf
          (if is_sim
           then ("@[message@ patterns@ of@ simulator@ may@ not@ bind@ " ^^
                 "source@ ports@ of@ variables@]")
           else ("@[message@ patterns@ matching@ adversarial@ and@ " ^^
                 "internal@ messages@ may@ not@ bind@ source@ ports@ " ^^
                 "to@ variables@]")))
  else check_add_const vid port_type si

let check_non_port_var_binding
    (abip : all_basic_inter_paths) (mp : string list) (mppl : EcLocation.t)
      : unit = 
  let d = List.exists (fun bp -> fst bp = mp) abip.direct in
  if d
  then type_error mppl
       (fun ppf ->
          fprintf ppf
          ("@[message@ patterns@ matching@ messages@ of@ direct@ " ^^
           "interfaces@ implemented@ by@ functionalities@ must@ bind@ " ^^
           "source@ ports@ to@ variables@]"))
  else ()

let check_item_type_add_binding
    (si : state_info) (mi : pat) (typ : typ) : state_info = 
  match mi with
  | PatWildcard _ -> si
  | PatId id      -> check_add_const id typ si

let rec get_loc_ty (ty : ty) : EcLocation.t = 
  match ty with
  | NamedTy id -> loc id
  | TupleTy tl -> mergeall (List.map (fun t -> get_loc_ty t) tl)

let get_loc_match_item (m_i : pat) : EcLocation.t = 
  match m_i with
  | PatWildcard l -> l
  | PatId id      -> loc id

let get_loc_match_item_list (tm : pat list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_match_item mi) tm)

let check_msg_content_bindings
    (bips : basic_inter_path list) (mp : string list * string)
    (tm : pat list) (si : state_info) : state_info = 
  let bip = List.find (fun p -> fst p = fst mp) bips in
  let mt =
    indexed_map_to_list
    (unlocm((unloc(IdMap.find (snd mp) (snd bip))).params_map)) in
  if List.length mt <> List.length tm
  then type_error (get_loc_match_item_list tm)
       (fun ppf ->
          fprintf ppf
          ("@[the@ number@ of@ argument@ patterns@ is@ different@ " ^^
           "from@ the@ number@ of@ message@ parameters@]"))
  else List.fold_left2 check_item_type_add_binding si tm mt

let check_pat_args
    (bips : basic_inter_path list) (msg_pat : msg_pat)
    (si : state_info) : state_info = 
  match msg_pat.pat_args with
  | None      -> si
  | Some pats -> 
      match msg_pat.msg_path_pat.msg_or_star with
      | MsgOrStarStar _ -> failure "cannot happen - check in parser"
      | MsgOrStarMsg id ->
          check_msg_content_bindings bips
          (unlocs msg_pat.msg_path_pat.inter_id_path, unloc id) pats si

let check_msg_pat
    (abip : all_basic_inter_paths) (msg_pat : msg_pat)
    (si : state_info) : state_info = 
  let abip = incoming_abip abip in
  let () = check_msg_path_pat abip msg_pat.msg_path_pat in
  let sv' =        
    match msg_pat.port_id with
    | Some id ->
        check_port_var_binding abip
        (unlocs msg_pat.msg_path_pat.inter_id_path) id si
    | None    ->
        let mppl = msg_path_pat_loc msg_pat.msg_path_pat in
        (check_non_port_var_binding abip 
         (unlocs msg_pat.msg_path_pat.inter_id_path) mppl;
         si) in
  let bips = flatten_all_basic_inter_paths abip in
  check_pat_args bips msg_pat sv'

let get_var_type (si : state_info) (id : id) : typ = 
  let vs =
    IdMap.union
    (fun _ _ ->
       failure
       ("Impossible! we already checked that params and " ^
        "vars have different names"))
    si.consts si.vars in
  IdMap.find (unloc id) vs

let check_initialized (si : state_info) (id : id) : unit = 
  let uid = unloc id in
  if IdMap.mem uid si.consts || IdSet.mem uid si.initialized_vs then ()
  else type_error (loc id)
       (fun ppf -> fprintf ppf "@[%s@ may@ not@ be@ initialized@]" uid)

let check_expr_var (si : state_info) (id : id) : typ = 
  let r = get_var_type si id in
  let () = check_initialized si id in
  r

let check_is_internal_port (si : state_info) (qid : qid) : bool =
  QidSet.mem (unlocs qid) si.internal_ports

let check_qid_type (si : state_info) (qid : qid) : typ = 
  try
    (match qid with
     | id :: [] -> check_expr_var si id
     | _        -> raise Not_found)
  with
  | Not_found -> 
      if check_is_internal_port si qid then port_type else raise Not_found

let check_expression (si : state_info) (expr : expression_l) : typ = 
  UcExpressions.check_expression (check_qid_type si) expr

let check_val_assign
    (si : state_info) (vid : id) (ex : expression_l) : state_info = 
  let etyp = check_expression si ex in
  check_assign_core vid etyp si

let check_sampl_assign
    (si : state_info) (vid : id) (ex : expression_l) : state_info = 
  let etyp = check_expression si ex in
  if not (UcExpressions.is_distribution etyp)
  then type_error (loc ex)
       (fun ppf ->
          fprintf ppf
          "@[you@ can@ sample@ only@ from@ distributions@]")
  else let dtyp = UcExpressions.get_distribution_typ etyp in 
       check_assign_core vid dtyp si

let check_transition (se : state_expr) (ss : state_sig IdMap.t)
                     (si : state_info) : unit = 
  let ssig = 
    try IdMap.find (unloc(se.id)) ss with
    | Not_found ->
        type_error (loc se.id)
        (fun ppf ->
           fprintf ppf "@[non-existing@ state:@ %s@]" (unloc se.id)) in
  let sp = ssig and args = se.args in
  if List.length sp <> List.length (unloc args)
  then type_error (loc args)
       (fun ppf -> fprintf ppf "@[wrong@ number@ of@ state@ arguments@]")
  else let te = List.combine sp (unloc args) in
       List.iteri
       (fun i (sigt, sip) -> 
          let et = check_expression si sip in
          if sigt <> et && sigt <> univ_type
          then type_error (loc sip)
               (fun ppf ->
                  fprintf ppf
                  ("@[parameter@ %d@ of@ state@ %s@ has@ type@ %a,@ " ^^
                   "which@ is@ incompatible@ with@ type@ %a@ " ^^
                   "of@ corresponding@ argument@]")
                   (i + 1) (unloc se.id) format_typ sigt format_typ et))
       te

let check_msg_arguments
    (mp : msg_path) (es : expression_l list located) (mc : typ_index IdMap.t)
    (si : state_info) : unit = 
  let sg = indexed_map_to_list (unlocm mc) in
  if List.length (unloc es) <> List.length sg
  then type_error (loc es)
       (fun ppf ->
          fprintf ppf "@[wrong@ number@ of@ message@ arguments@]")
  else List.iter2i
       (fun i ex typ ->
          let tex = check_expression si ex in
          if not (tex = typ)
          then type_error (loc ex)
               (fun ppf ->
                  fprintf ppf
                  ("@[parameter@ %d@ of@ message@ %s@ has@ type@ %a,@ " ^^
                   "which@ is@ incompatible@ with@ type@ %a@ " ^^
                   "of@ corresponding@ argument@]")
                  (i + 1) (string_of_msg_path mp) format_typ typ
                  format_typ tex))
       (unloc es) sg

let check_send_direct
    (msg : msg_expr) (mc : typ_index IdMap.t) (si : state_info) : unit = 
  let l = msg_path_loc msg.path in
  let () =
    match msg.port_id with
    | Some p ->
        (check_declared_with_compatible_type p port_type si;
         check_initialized si p)
    | None   ->
        type_error l
        (fun ppf ->
           fprintf ppf "@[missing@ destination@ port@]") in
  check_msg_arguments msg.path msg.args mc si

let check_send_adversarial
    (msg : msg_expr) (mc : typ_index IdMap.t) (si : state_info) : unit = 
  let l = msg_path_loc msg.path in
  let () =
    match msg.port_id with
    | Some _ ->
        type_error l
        (fun ppf ->
           fprintf ppf
           "@[only@ direct@ messages@ can@ have@ destination@ ports@]")
    | None   -> () in
  check_msg_arguments msg.path msg.args mc si

let check_send_internal (msg : msg_expr) (mc : typ_index IdMap.t)
                        (si : state_info) : unit = 
  let l = msg_path_loc msg.path in
  let () =
    match msg.port_id with
    | Some _ ->
        type_error l
        (fun ppf ->
           fprintf ppf
           ("@[messages@ to@ subfunctionalities@ cannot@ have@ " ^^
            "destination@ ports@]"))
    | None -> () in
  check_msg_arguments msg.path msg.args mc si

let is_msg_path_inb_inter_id_paths
    (mp : msg_path) (abip : basic_inter_path list) : bool = 
  let bpo = List.find_opt (fun bp -> fst bp = unlocs mp.inter_id_path) abip in
  match bpo with
  | Some _ -> true
  | None   -> false

let get_msg_def_for_msg_path
    (mp : msg_path) (bs : basic_inter_path list) : message_def_body_tyd = 
  let iop = unlocs mp.inter_id_path in
  let bio = List.find (fun bp -> fst bp = iop) bs in
  let umid = unloc mp.msg in
  let mdb = IdMap.find umid (snd bio) in
  unloc mdb

let check_send_msg_path
    (msg : msg_expr) (abip : all_basic_inter_paths) : unit =
  let abip = outgoing_abip abip in
  check_outgoing_msg_path abip msg.path

let check_send (msg : msg_expr) (abip : all_basic_inter_paths)
               (si : state_info) : unit = 
  let () = check_send_msg_path msg abip in
  let bs = abip.direct @ abip.adversarial @ abip.internal in
  let mdbc = (get_msg_def_for_msg_path msg.path bs).params_map in
  match msg.path with
  | ( _ as p) when is_msg_path_inb_inter_id_paths p abip.direct ->
      check_send_direct msg mdbc si
  | ( _ as p) when is_msg_path_inb_inter_id_paths p abip.adversarial ->
      check_send_adversarial msg mdbc si
  | ( _ as p) when is_msg_path_inb_inter_id_paths p abip.internal ->
      check_send_internal msg mdbc si
  | _ ->
      failure
      ("impossible - the path is always in one of direct|" ^
       "adversarial|internal") 

let check_send_and_transition
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sat : send_and_transition) (si : state_info)
      : unit = 
  let () = check_send sat.msg_expr abip si in
  check_transition sat.state_expr ss si

let merge_state_info (sv1 : state_info) (sv2 : state_info) : state_info = 
  {flags = sv1.flags; internal_ports = sv1.internal_ports;
   consts = sv1.consts; vars = sv1.vars;
   initialized_vs = IdSet.inter sv1.initialized_vs sv2.initialized_vs}

let rec check_ite
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info)
    (ex : expression_l) (tins : instruction_l list located)
    (eins : instruction_l list located option)
      : state_info = 
  if check_expression si ex <> bool_type
  then type_error (loc ex)
       (fun ppf ->
          fprintf ppf
          "@[the@ condition@ must@ be@ a@ boolean expression@]")
  else check_branches abip ss si tins eins

and check_branches
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (tins : instruction_l list located)
    (eins : instruction_l list located option)
      : state_info = 
  let tsv = check_instructions abip ss si tins in
  let esv =
    match eins with                         
    | Some is -> check_instructions abip ss si is
    | None    -> si in
  merge_state_info tsv esv

and check_decode
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (ex : expression_l) (ty : ty)
    (m_is : pat list) (okins : instruction_l list located)
    (erins : instruction_l list located)
      : state_info = 
  if check_expression si ex <> univ_type
  then type_error (loc ex)
       (fun ppf ->
          fprintf ppf "@[only@ expressions@ of@ univ@ type@ can@ be@ decoded@]")
  else let dt =
         match check_type ty with
         | Tconstr (x, y) -> [Tconstr (x,y)]
         | Ttuple  t      -> t
         | _              ->
             failure
             "check_type is supposed to return only Tconstr or Ttuple." in
       if List.length m_is <> List.length dt
       then type_error (get_loc_match_item_list m_is)
            (fun ppf ->
               fprintf ppf
               ("@[the@ number@ of@ bindings@ is@ different@ from@ the@ " ^^
                "arity@ of@ decoded@ type@]"))
       else let sv' = List.fold_left2 check_item_type_add_binding si m_is dt in
            check_branches abip ss sv' okins (Some erins)

and check_instruction
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (i : instruction_l)
      : state_info = 
  match unloc i with
  | Assign (vid, ex)                    -> check_val_assign si vid ex
  | Sample (vid, ex)                    -> check_sampl_assign si vid ex
  | ITE (ex, tins, eins)                -> check_ite abip ss si ex tins eins
  | Decode (ex, ty, m_is, okins, erins) ->
      check_decode abip ss si ex ty m_is okins erins
  | SendAndTransition sat               ->
      (check_send_and_transition abip ss sat si; si)
  | Fail                                -> si

and check_instructions
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (is : instruction_l list located)
      : state_info = 
  let uis = unloc is in
  List.fold_left (check_instruction abip ss) si uis

let illegal_control_transfer (l : EcLocation.t) =
  type_error l
  (fun ppf ->
     fprintf ppf
     ("@[control@ transfer@ by@ \"fail\"@ or@ \"send-and-transition\"@ " ^^
      "instruction@ is@ only@ allowed@ at@ end@ of@ message@ match@ clause@]"))

let failure_to_transfer_control (l : EcLocation.t) =
  type_error l
  (fun ppf ->
     fprintf ppf
     ("@[message@ match@ clause@ must@ end@ with@ control@ transfer@ via@ " ^^
      "\"fail\"@ or@ \"send-and-transition\"@ instruction@]"))

let rec check_instrs_transfer_at_end (is : instruction_l list located) : unit =
  let uis = unloc is in
  match uis with
  | [] -> failure_to_transfer_control (loc is)
  | is ->
      let xs = List.take (List.length is - 1) is in
      (List.iter check_instr_not_transfer xs;
       check_instr_end_in_transfer (List.last is))

and check_instrs_not_transfer (is : instruction_l list located) : unit =
  let uis = unloc is in
  List.iter check_instr_not_transfer uis

and check_instr_end_in_transfer (instr : instruction_l) : unit =
  let uinstr = unloc instr in
  match uinstr with
  | Assign _                    -> failure_to_transfer_control (loc instr)
  | Sample _                    -> failure_to_transfer_control (loc instr)
  | SendAndTransition _         -> ()
  | Fail                        -> ()
  | ITE (_, thens, elses)       ->
      (check_instrs_transfer_at_end thens;
       match elses with
       | None       -> failure_to_transfer_control (loc instr)
       | Some elses -> check_instrs_transfer_at_end elses)
  | Decode (_, _, _, oks, nots) ->
      (check_instrs_transfer_at_end oks;
       check_instrs_transfer_at_end nots)

and check_instr_not_transfer (instr : instruction_l) : unit =
  let uinstr = unloc instr in
  match uinstr with
  | Assign _                    -> ()
  | Sample _                    -> ()
  | SendAndTransition _         -> illegal_control_transfer (loc instr)
  | Fail                        -> illegal_control_transfer (loc instr)
  | ITE (_, thens, elses)       ->
      (check_instrs_not_transfer thens;
       match elses with
       | None       -> ()
       | Some elses -> check_instrs_not_transfer elses)
  | Decode (_, _, _, oks, nots) ->
      (check_instrs_not_transfer oks;
       check_instrs_not_transfer nots)

let check_msg_match_code
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (is : instruction_l list located)
      : unit = 
  let () = ignore (check_instructions abip ss si is) in
  check_instrs_transfer_at_end is

let check_msg_match_clause
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (mmc : msg_match_clause) : unit = 
  let sv' = check_msg_pat abip mmc.msg_pat si in
  check_msg_match_code abip ss sv' mmc.code

let check_state_code
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (si : state_info) (mmclauses : msg_match_clause list)
      : unit =
  let () =
    List.iter (fun mmc -> check_msg_match_clause abip ss si mmc) mmclauses in
  check_msg_match_deltas abip
  (List.map (fun mmc -> mmc.msg_pat) mmclauses)

let get_keys (m : 'a IdMap.t) : QidSet.t = 
  let lp = fst(List.split (IdMap.bindings m)) in
  List.fold_left (fun s p -> QidSet.add [p] s) QidSet.empty lp

let get_internal_ports (r_f : fun_body_tyd) : QidSet.t = 
  QidSet.union
  (get_keys (parties_of_fun_body_tyd r_f))
  (QidSet.union (get_keys (params_of_fun_body_tyd r_f))
                (get_keys (sub_funs_of_fun_body_tyd r_f)))

let filterb_inter_id_paths
    (abip : basic_inter_path list) (pfxs : string list located list)
      : basic_inter_path list = 
  List.filter
  (fun bp -> List.exists (fun pfx -> unloc pfx = fst bp) pfxs)
  abip

let get_fb_inter_id_paths
   (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
   (f : fun_tyd) : all_basic_inter_paths = 
  let uf = unloc f in
  let iddir = id_dir_inter_of_fun_body_tyd uf in
  let direct = get_basic_inter_paths_from_inter_id iddir dir_inter_map in
  let adversarial = 
    match id_adv_inter_of_fun_body_tyd uf with
    | Some id -> get_basic_inter_paths_from_inter_id id adv_inter_map
    | None    -> [] in
  {direct = direct; adversarial = adversarial; internal = []}

let get_all_basic_inter_paths
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
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
           let did = get_dir_inter_id_impl_by_fun_id (unloc sf) funs in
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

let check_state
    (ur_f : fun_body_tyd) (states : state_tyd IdMap.t)
    (abip : all_basic_inter_paths) (s : state_tyd) : unit = 
  let us = unloc s in
  let sv = init_state_info (unloc s) (get_internal_ports ur_f) [] in
  let ss = get_state_sigs states in
  check_state_code abip ss sv us.mmclauses

let check_fun (maps : maps_tyd) (fund : fun_def) : maps_tyd =
  let uid = unloc fund.id in
  let () =
    if exists_id_maps_tyd maps uid
    then type_error (loc fund.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
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
      let params =
        check_real_fun_params maps.dir_inter_map maps.adv_inter_map
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
             type_error (loc dup.id)
             (fun ppf ->
                fprintf ppf
                ("@[the@ name@ %s@ is@ the@ same@ name@ as@ one@ of@ the@ " ^^
                 "functionality's@ parameters@]")
                id) in
      let check_sub_fun_decl (sf : sub_fun_decl) : id =
        let uid = unloc sf.id in
        let ufun_id = unloc sf.fun_id in
        match IdMap.find_opt ufun_id maps.fun_map with
        | None    ->
            type_error (loc sf.fun_id)
            (fun ppf ->
               fprintf ppf
               "@[nonexisting@ functionality:@ %s@]" ufun_id)
        | Some ft ->
            let fbt = unloc ft in
            if exists_id_inter_maps maps.dir_inter_map maps.adv_inter_map
               uid
              then type_error (loc sf.id)
                   (fun ppf ->
                      fprintf ppf
                      ("@[subfunctionality@ name@ may@ not@ be@ same@ as@ " ^^
                       "top-level@ interface@ name@]"))
            else if is_real_fun_body_tyd fbt
              then type_error (loc sf.fun_id)
                   (fun ppf ->
                      fprintf ppf
                      "@[%s@ is@ not@ an@ ideal@ functionality@]" ufun_id)
            else mk_loc (loc sf.id) ufun_id in
      let sub_funs = IdMap.map check_sub_fun_decl sub_fun_decls in
      let party_defs =
        check_unique_ids
        (fun ppf -> fprintf ppf "@[duplicate@ party@ name@]")
        fbr.party_defs
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
      let () =
        IdMap.iter
        (fun _ p -> 
           let up = unloc p in
           let abip =
             get_all_basic_inter_paths
             maps.dir_inter_map maps.adv_inter_map maps.fun_map ft p in
           let states = up.states in
           IdMap.iter
           (fun _ -> check_state (unloc ft) states abip)
           states)
        parties in
      {maps with
         fun_map =
           IdMap.add uid ft maps.fun_map}
  | FunBodyIdeal state_defs ->
      let states =
        match fund.id_adv with
        | None ->
            type_error (loc fund.id)
            (fun ppf ->
               fprintf ppf
               ("@[an@ ideal@ functionality@ must@ implement@ a@ basic@ " ^^
                "adversarial@ interface@]"))
        | Some id ->
            (check_exists_inter AdversarialInterKind maps.adv_inter_map id;
             check_is_basic AdversarialInterKind maps.adv_inter_map id;
             check_toplevel_states fund.id state_defs) in
      let ifbt =
        {id_dir_inter = uid_dir_inter; id_adv_inter = Option.get uid_adv_inter;
         states = states} in
      let ft = mk_loc (loc fund.id) (FunBodyIdealTyd ifbt) in
      let () =
        let states = ifbt.states in
        let abip =
          get_fb_inter_id_paths maps.dir_inter_map maps.adv_inter_map
          ft in
        IdMap.iter
        (fun _ -> check_state (unloc ft) states abip)
        states in
      {maps with
         fun_map =
           IdMap.add uid
           (mk_loc (loc fund.id) (FunBodyIdealTyd ifbt))
           maps.fun_map}

(****************************** simulator checks ******************************)

let check_msg_code_sim
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (mmc : msg_match_clause) (si : state_info)
      : unit = 
  check_msg_match_code abip ss si mmc.code

let check_message_path_sim
    (bip : basic_inter_path list) (isini : bool)
    (mmc : msg_match_clause) : unit = 
  let bip = filter_dir_basic_inter_paths In bip in
  let mpp = mmc.msg_pat.msg_path_pat in
  let l = msg_path_pat_loc mpp in
  let id = fst (List.find (fun p -> List.length (fst p) = 1) bip) in
  if isini && unlocs mpp.inter_id_path <> id
  then type_error l
       (fun ppf ->
          fprintf ppf
          ("@[initial@ state@ can@ handle@ only@ messages@ comming@ " ^^
           "from@ ideal@ functionality;@ did@ you@ omit@ prefix@ %s?@]")
          (List.hd id))
  else let iops = fst (List.split bip) in
       let invalid_dest () =
         type_error l
         (fun ppf ->
            fprintf ppf
            ("@[not@ a@ valid@ message@ interface@ path;@ these@ paths@ " ^^
             "are@ valid:@;<1 2>%a@]")
            format_id_paths_comma iops) in
       let umpiop = (unlocs mpp.inter_id_path) in
       match mpp.msg_or_star with
       | MsgOrStarMsg mt ->
           if not(List.mem umpiop iops)
             then invalid_dest ()
           else if List.exists
                   (fun bp ->
                          fst bp = umpiop &&
                          IdMap.mem (unloc mt) (snd bp))
                   bip
             then ()
           else type_error (loc mt)
                (fun ppf ->
                   fprintf ppf
                   "@[%s@ is@ not@ an@ incoming@ message@ of@ %s@]"
                   (unloc mt) (string_of_id_path umpiop))
       | MsgOrStarStar _ ->
           if List.exists
              (fun p -> sl1_starts_with_sl2 p umpiop)
              iops
           then ()
           else invalid_dest ()

let check_match_bindings_sim
    (abip : basic_inter_path list) (si : state_info)
    (mmc : msg_match_clause) : state_info = 
  let mm = mmc.msg_pat in
  check_pat_args abip mm si

let check_msg_match_deltas_sim
    (abip : all_basic_inter_paths) (isini : bool) (uid_uses : string)
    (mmclauses : msg_match_clause list)
      : unit = 
  let abip = incoming_abip abip in
  let r =
    msg_match_deltas abip
    (List.map
     (fun mmc ->
        {inter_id_path = mmc.msg_pat.msg_path_pat.inter_id_path;
         msg_or_star   = mmc.msg_pat.msg_path_pat.msg_or_star})
    mmclauses) in
  let r =
    if isini
    then List.filter
         (fun mp -> unloc (List.hd mp.inter_id_path) = uid_uses)
         r
    else r in
  if r <> []
  then let l = msg_path_pat_loc (List.last mmclauses).msg_pat.msg_path_pat in
       type_error l
       (fun ppf ->
          fprintf ppf
          ("@[message patterns are not exhaustive; these " ^^
           "messages are not matched:@;<1 2>%a@]")
          format_msg_path_list r)

let check_sim_state_code
    (bips : basic_inter_path list) (ss : state_sig IdMap.t)
    (si : state_info) (isini : bool) (uid_uses : string)
    (mmclauses : msg_match_clause list)
      : unit = 
  let () = List.iter (check_message_path_sim bips isini) mmclauses in
  let svs = List.map (check_match_bindings_sim bips si) mmclauses in
  let abip = {direct = []; adversarial = bips; internal = []} in
  let () = List.iter2 (check_msg_code_sim abip ss) mmclauses svs in
  check_msg_match_deltas_sim abip isini uid_uses mmclauses

let get_sim_components
    (fun_map : fun_tyd IdMap.t) (r_f : string)
    (args : string list) : fun_body_tyd QidMap.t = 
  let urf = unloc (IdMap.find r_f fun_map) in
  let qidmap_fun = QidMap.singleton [r_f] urf in
  let qidmap_params =
    let pids =
      IdMap.fold (fun pid _ l -> pid :: l) (params_of_fun_body_tyd urf) [] in
    List.fold_left2
    (fun mp pid fid ->
       let fbt = unloc (IdMap.find fid fun_map) in
       QidMap.add [r_f; pid] fbt mp)
    QidMap.empty pids args in
  let qidmap_subfuns =
    IdMap.fold
    (fun sfid sfd mp ->
       let sfd_fbt = unloc (IdMap.find (unloc sfd) fun_map) in
       QidMap.add [r_f; sfid] sfd_fbt mp)
    (sub_funs_of_fun_body_tyd urf) QidMap.empty in
  let disj = (fun _ _ _ -> failure "cannot happen") in
  QidMap.union disj qidmap_fun (QidMap.union disj qidmap_params qidmap_subfuns)
                
let get_component_adv_inter_id_paths
    (adv_inter_map : inter_tyd IdMap.t) (f : fun_body_tyd)
      : basic_inter_path list = 
  match id_adv_inter_of_fun_body_tyd f with
  | Some id -> get_basic_inter_paths_from_inter_id id adv_inter_map 
  | None    -> []

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In

let invert_mdf (mdf : message_def_body_tyd) : message_def_body_tyd = 
  {dir = invert_dir mdf.dir;
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

let get_sim_basic_inter_id_paths
    (adv_inter_map : inter_tyd IdMap.t) (uses : string)
    (cs : fun_body_tyd QidMap.t) : basic_inter_path list = 
  let sbps = QidMap.map (get_component_adv_inter_id_paths adv_inter_map) cs in
  let bps =
    QidMap.add
    []
    (List.map invert_msg_dirs
     (get_basic_inter_paths_from_inter_id uses adv_inter_map))
    sbps in
  QidMap.fold
  (fun q bpl l -> l @ List.map (fun bp -> (q @ fst bp, snd bp)) bpl)
  bps []

let get_sim_internal_ports (cs : fun_body_tyd QidMap.t) : QidSet.t = 
  let rcsips = QidMap.map (fun fb -> get_internal_ports fb) cs in
  let rcsqips =
    QidMap.mapi (fun q ips -> QidSet.map (fun ip -> q @ ip) ips) rcsips in
  QidMap.fold (fun _ qips sip -> QidSet.union qips sip) rcsqips QidSet.empty
        
let check_sim_code
    (adv_inter_map : inter_tyd IdMap.t) (funs : fun_tyd IdMap.t)
    (sim : sim_def_tyd) : unit = 
  let usim = unloc sim in
  let states = usim.states in
  let ss = get_state_sigs states in
  let cs = get_sim_components funs usim.sims usim.sims_arg_ids in
  let bps = get_sim_basic_inter_id_paths adv_inter_map usim.uses cs in
  IdMap.iter
  (fun _ s -> 
     let us = unloc s in
     let sv =
       init_state_info us (get_sim_internal_ports cs) ["simulator"] in
     check_sim_state_code bps ss sv us.is_initial usim.uses us.mmclauses)
  states

let check_exists_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let urf = unloc rf in
  if exists_id funs urf then ()
  else type_error (loc rf)
       (fun ppf -> fprintf ppf "@[functionality@ isn't@ defined:@ %s@]" urf)

let check_is_real_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let () = check_exists_f funs rf in
  let f = unloc (IdMap.find (unloc rf) funs) in
  if not (is_real_fun_body_tyd f)
  then type_error (loc rf)
       (fun ppf ->
          fprintf ppf
          "@[the@ simulated@ functionality@ must@ be@ a@ real@ functionality@]")

let check_sim_fun_args
    (funs : fun_tyd IdMap.t) (_ : inter_tyd IdMap.t)
    (rf : id) (params : id list located) = 
  let d_ios = get_params_of_real_fun_id funs (unloc rf) in
  let d_ios' =
    List.map
    (fun id ->
       get_dir_inter_id_impl_by_fun_id id funs) (unlocs (unloc params)) in
  if List.length d_ios <> List.length d_ios'
  then type_error (loc params)
       (fun ppf ->
          fprintf ppf
          "@[wrong@ number@ of@ arguments@ for@ functionality@]")
  else let () =
         List.iteri
         (fun i pid ->
          if List.nth d_ios i <> List.nth d_ios' i
          then type_error (loc pid)
               (fun ppf ->
                  fprintf ppf
                  ("@[argument@ %d@ implements@ composite@ direct@ " ^^
                   "interface@ %s,@ whereas@ it@ should@ implement@ %s@]")
                  (i + 1) (List.nth d_ios' i) (List.nth d_ios i)))
         (unloc params) in
       List.iter
       (fun pid ->
              let f = unloc (IdMap.find (unloc pid) funs) in
              match f with
              | FunBodyRealTyd _ ->
                  type_error (loc pid)
                  (fun ppf ->
                     fprintf ppf
                     ("@[the@ argument@ to@ simulated@ functionality@ must@ " ^^
                      "be@ an@ ideal@ functionality@]"))
              | FunBodyIdealTyd _  ->
                  (* we know the ideal functionality implements a basic
                     adversarial interface *)
                  ())
       (unloc params)

let check_sim_decl
    (adv_inter_map : inter_tyd IdMap.t)
    (fun_map : fun_tyd IdMap.t) (sd : sim_def) : sim_def_tyd = 
  let () = check_exists_inter AdversarialInterKind adv_inter_map sd.uses in
  let () = check_is_basic AdversarialInterKind adv_inter_map sd.uses in
  let uses = unloc sd.uses in
  let () = check_is_real_f fun_map sd.sims in
  let sims = unloc sd.sims in
  let () = List.iter (check_exists_f fun_map) (unloc sd.sims_arg_ids) in
  let () =
    check_sim_fun_args fun_map adv_inter_map sd.sims sd.sims_arg_ids in
  let sims_arg_ids = unlocs (unloc sd.sims_arg_ids) in
  let body = check_toplevel_states sd.id sd.states in
  mk_loc (loc sd.id)
  {uses = uses; sims = sims; sims_arg_ids = sims_arg_ids; states = body}

let check_sim (maps : maps_tyd) (simd : sim_def) : maps_tyd =
  let uid = unloc simd.id in
  let () =
    if exists_id_maps_tyd maps uid
    then type_error (loc simd.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let sdt = check_sim_decl maps.adv_inter_map maps.fun_map simd in
  let () = check_sim_code  maps.adv_inter_map maps.fun_map sdt in
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
           (fun ppf ->
              fprintf ppf
              ("@[EasyCrypt@ theory@ to@ be@ imported@ must@ begin@ with@ " ^^
               "uppercase@ letter:@ %s@]")
              uid) in
    try UcEcInterface.require_import (unloc id) with
    Failure f ->
      type_error (loc id)
      (fun ppf ->
         fprintf ppf
         "@[error@ when@ importing@ EasyCrypt@ theory@ %s:@ \"%s\"@]"
         (unloc id) f) in
  List.iter reqimp reqs

let typecheck spec = 
  let () = UcEcInterface.init() in
  let () = load_ec_reqs spec.externals.ec_requires in
  check_defs spec.definitions
