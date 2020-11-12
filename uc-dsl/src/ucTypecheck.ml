(* UcTypecheck module *)

(* Typecheck a specification *)

open Batteries
open Format
open EcLocation
open EcParsetree
open UcSpec
open UcTypedSpec
open UcUtils
open UcMessage

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
       type_error (loc id_l)
       (fun ppf -> fprintf ppf "@[%t:@ %s@]" msgf (unloc id_l))
     else IdMap.add (unloc id_l) a id_map)
  id_map al

(* EasyCrypt type checks *)

let env () = UcEcInterface.env ()

let check_type (pty : pty) : EcTypes.ty =
  let ue = EcUnify.UniEnv.create None in
  EcTyping.transty EcTyping.tp_nothing (env ()) ue pty
  
let check_name_type_bindings
    (msgf : formatter -> unit) (ntl : type_binding list)
      : ty_index IdMap.t = 
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
         (fun ppf -> fprintf ppf "@[duplicate@ message@ parameter@ name@]")
         md.params;
       port = match md.port with
              | Some p -> Some (unloc p)
              | None   -> None          })
  msg_map)

let check_comp_item
    (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
    (ci : comp_item) : psymbol = 
  let uid = unloc ci.inter_id in
  match IdMap.find_opt uid inter_map with
  | None    -> 
      type_error
      (loc ci.inter_id)
      (fun ppf ->
         fprintf ppf
         "@[%s@ isn't@ %s@ interface@ name@]" uid (inter_kind_to_str true ik))
  | Some it ->
      let ibt = unloc it in
      if is_composite_tyd ibt
      then type_error (loc ci.inter_id)
           (fun ppf ->
              fprintf ppf
              "@[%s@ isn't@ a@ basic@ interface@]" uid)
      else mk_loc (loc ci.sub_id) (unloc ci.inter_id)

let check_comp_inter
    (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
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
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let ibt =
    match ni.inter with
    | Basic mds     -> check_basic_inter mds
    | Composite cis -> check_comp_inter ik inter_map cis in
  let it = mk_loc (loc ni.id) ibt in
  IdMap.add uid it inter_map
                
let check_inter_def (maps : maps_tyd) (interd : inter_def) : maps_tyd =
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
(*
let check_exists_inter
    (ik : inter_kind) (inter_map : inter_tyd IdMap.t) (id : id) : unit = 
  let uid = unloc id in
  if exists_id inter_map uid then () 
  else type_error (loc id)
       (fun ppf ->
          fprintf ppf
          "@[%s@ interface@ does@ not@ exist:@ %s@]"
          (inter_kind_to_str false ik) uid)

(* the following two functions assume id exists in inter_map *)

let check_is_basic
    (ik : inter_kind) (inter_map : inter_tyd IdMap.t)
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

(**************************** state machine checks ****************************)

(* typechecking context for states

   constants and local variables are disjoint

   in real functionalities, internal ports have the form [Party], were
   Party is the name of one of the functionality's parties; in this
   case Party is not a constant or local variable

   in simulators, when internal ports have length 2, and begin with
   the name of the real functionality that is being simulated, there
   is no chance of overlap with constants and local variables

   consequently, when constants, local variables and internal port
   names are used in expressions, there is no ambiguity *)

type state_context =
  {initial : bool;             (* initial state? *)
   flags : string list;        (* flags used to customize checking *)
   internal_ports : QidSet.t;  (* internal port names - names of parties *)
   consts : typ IdMap.t;       (* constants: state parameters and bound in
                                  patterns *)
   vars : typ IdMap.t}         (* local variables *)

(* static analysis information for states *)

type state_analysis =
  {initialized_vs : IdSet.t}  (* definitely initialized variables *)

let init_state_context
    (s : state_body_tyd) (ports : QidSet.t)
    (flags : string list) : state_context = 
  let consts = IdMap.map (fun p -> fst (unloc p)) s.params in
  let vars = IdMap.map (fun v -> unloc v) s.vars in
  {initial = s.is_initial; flags = flags; internal_ports = ports;
   consts = consts; vars = vars}

let init_state_analysis : state_analysis =
  {initialized_vs = IdSet.empty}

(* state signatures - lists of the types of each state's parameters *)

type state_sig = typ list

let get_state_sig (s : state_body_tyd) : state_sig = 
  if s.is_initial then []
  else let ps = IdMap.bindings s.params in
       let ts = unlocs (snd (List.split ps)) in
       let tord = List.sort (fun t1 t2 -> snd t1 - snd t2) ts in
       (fst (List.split tord))

let get_state_sigs (states : state_tyd IdMap.t) : state_sig IdMap.t = 
  IdMap.map (fun s -> get_state_sig (unloc s)) states

(* a basic_inter_path will have the form (ids, b), where we call ids
   an inter id path:

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
   real functionality's parameters' and subfunctionalities' direct
   interfaces) *)

type all_basic_inter_paths =
  {direct : basic_inter_path list; adversarial : basic_inter_path list;
   internal : basic_inter_path list}

let flatten_all_basic_inter_paths (abip : all_basic_inter_paths)
      : basic_inter_path list = 
  abip.direct @ abip.adversarial @ abip.internal

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

(* root can be the same as inter_id, but it can also be the name of
   a functionality parameter or subfunctionality *)

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

let get_external_inter_id_paths
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t) :
      string list list = 
  let dir = get_inter_id_paths_from_inter_id id_dir_inter dir_inter_map in
  let adv =
    match id_adv_inter with
    | Some id -> get_inter_id_paths_from_inter_id id adv_inter_map
    | None    -> [] in
  dir @ adv

let invert_basic_inter_path (bip : basic_inter_path) : basic_inter_path = 
  let bibt = snd bip in
  let bibt_inv = invert_basic_inter_body_tyd bibt in
  (fst bip, bibt_inv)

let check_inter_id_paths_unique
    (msgf : formatter -> unit) (idps : string list located list) : unit = 
  ignore
  (List.fold_left
   (fun l idp -> 
      let uidp = unloc idp in
      if List.mem uidp l
      then type_error (loc idp) msgf
      else uidp :: l)
   [] idps)

let check_inter_id_path
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (iidp : id list) : string list located = 
  let uidp = unlocs iidp in
  let loc = mergelocs iidp in
  let ps =
    get_external_inter_id_paths id_dir_inter id_adv_inter
    dir_inter_map adv_inter_map in
  if List.mem uidp ps
  then mk_loc loc uidp
  else type_error loc
       (fun ppf ->
          fprintf ppf
          ("@[the@ party@ must@ serve@ sub-interfaces@ of@ the@ " ^^
           "composite@ interfaces@ implemented@ by@ the@ " ^^
           "functionality:@;<1 2>%a@]")
          format_id_paths_comma ps)

let check_served_inter_id_paths
    (serves : string list located list)
    (id_dir_inter : string) (party_id : id) : unit = 
  let er ppf =
    fprintf ppf
    ("@[a@ party@ must@ serve@ one@ basic@ direct@ interface,@ and@ may@ " ^^
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
      else type_error (mergelocs serves) er
  | _ -> type_error (mergelocs serves) er

let check_inter_id_paths_coverage
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (served_ps : string list located list) : unit = 
  let serps = unlocs served_ps in
  let ps =
    get_external_inter_id_paths id_dir_inter id_adv_inter
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

let check_parties_serve_coverage_and_distinct
    (parties : party_def_tyd IdMap.t)
    (id_dir_inter : string) (id_adv_inter : string option)
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
      : unit = 
  let served_ps =
    IdMap.fold (fun _ p l -> l @ (unloc p).serves) parties [] in
  let () =
    check_inter_id_paths_unique
    (fun ppf ->
       fprintf ppf
       "@[parties@ must@ serve@ distinct@ sub-interfaces@]")
    served_ps in
  check_inter_id_paths_coverage id_dir_inter id_adv_inter
  dir_inter_map adv_inter_map served_ps

(* message paths and message path patterns *)

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
           "message@ paths:@;<1 2>%a@]")
       format_msg_path_list allps)

let check_msg_path_pat
    (abip : all_basic_inter_paths) (sc : state_context)
    (mpp : msg_path_pat) : unit = 
  let init_and_sim = sc.initial && List.mem "simulator" sc.flags in
  let allmps = msg_paths_of_all_basic_inter_paths abip in       
  let restrmps =
    if init_and_sim
    then List.filter
         (fun mps -> List.length mps.inter_id_path = 1)
         allmps
    else allmps in
  match mpp.msg_or_star with
  | MsgOrStarMsg _  -> 
      if List.exists
         (fun mp -> string_of_msg_path mp = string_of_msg_path_pat mpp)
         restrmps
        then ()
      else if List.exists  (* will be initial state of simulator *)
              (fun mp -> string_of_msg_path mp = string_of_msg_path_pat mpp)
              allmps
        then type_error (msg_path_pat_loc mpp)
             (fun ppf ->
                fprintf ppf
                ("@[message@ path@ is@ not@ one@ of@ the@ possible@ " ^^
                 "incoming@ message@ paths@ for@ initial@ state@ " ^^
                 "of@ simulator:@;<1 2>%a@]")
                format_msg_path_list restrmps)        
      else type_error (msg_path_pat_loc mpp)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ is@ not@ one@ of@ the@ possible@ " ^^
               "incoming@ message@ paths:@;<1 2>%a@]")
              format_msg_path_list restrmps)
  | MsgOrStarStar _ ->
      if (List.exists
          (fun mp -> qid1_starts_with_qid2 mp.inter_id_path mpp.inter_id_path)
          restrmps)
        then ()
      else if (List.exists  (* will be initial state of simulator *)
              (fun mp ->
                 qid1_starts_with_qid2 mp.inter_id_path mpp.inter_id_path)
              allmps)
        then type_error (msg_path_pat_loc mpp)
             (fun ppf ->
                fprintf ppf
                ("@[message@ path@ pattern@ is@ inconsistent@ with@ the@ " ^^
                 "paths@ of@ possible@ incoming@ messages@ for@ initial@ " ^^
                 "state@ of@ simulator:@;<1 2>%a@]")
                 format_msg_path_list restrmps)
      else type_error (msg_path_pat_loc mpp)
           (fun ppf ->
              fprintf ppf
              ("@[message@ path@ pattern@ is@ inconsistent@ with@ the@ " ^^
               "paths@ of@ possible@ incoming@ messages:@;<1 2>%a@]")
               format_msg_path_list restrmps)

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

let coverage_msg_path_pats
    (abip : all_basic_inter_paths) (sc : state_context)
    (mpps : msg_path_pat list) : msg_path list = 
  let allmps = msg_paths_of_all_basic_inter_paths abip in
  let allmps =
    if sc.initial && List.mem "simulator" sc.flags
    then List.filter
         (fun mps -> List.length mps.inter_id_path = 1)
         allmps
    else allmps in
  List.fold_left (fun mps mp -> remove_covered_paths mps mp) allmps mpps

let check_coverage_msg_path_pats
    (abip : all_basic_inter_paths) (sc : state_context)
    (mml : msg_pat list) : unit = 
  let abip = incoming_abip abip in
  let r =
    coverage_msg_path_pats abip sc
    (List.map (fun (mm : msg_pat) -> mm.msg_path_pat) mml) in
  if r <> []
  then let l = msg_path_pat_loc (List.last mml).msg_path_pat in
       type_error l
       (fun ppf ->
          fprintf ppf
          ("@[message@ patterns@ are@ not@ exhaustive;@ these@ " ^^
           "messages@ are@ not@ matched:@;<1 2>%a@]")
          format_msg_path_list r)

(* working with variables and constants *)

let get_declared (sc : state_context) = 
  IdMap.union
  (fun _ _ _ ->
     failure
     ("@[impossible,@ we@ already@ checked@ params@ and@ local@ " ^
      "vars@ have@ different@ ids@]"))
  sc.consts sc.vars

let check_declared_with_compatible_type
    (id : id) (typ : typ) (sc : state_context) : unit = 
  let uid = unloc id in
  let decs = get_declared sc in
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
    (vid : id) (typ : typ) (sc : state_context)
    (sa : state_analysis) : state_analysis = 
  let uvid = unloc vid in
  if not (IdMap.mem uvid sc.vars)
  then type_error (loc vid)
       (fun ppf -> fprintf ppf ("@[%s@ is@ not@ a@ declared@ variable@]") uvid)
  else (check_declared_with_compatible_type vid typ sc;
        {sa with
           initialized_vs = IdSet.add uvid sa.initialized_vs})

(* constants can be rebound, in new scopes; but they may not eclipse
   variables or internal port names *)

let check_add_const (id : id) (typ : typ) (sc : state_context)
      : state_context = 
  let uid = unloc id in
  if IdMap.mem uid sc.vars
    then type_error (loc id)
         (fun ppf ->
            fprintf ppf
            "@[cannot@ rebind@ variable@ name@ in@ pattern@]")
  else if QidSet.mem [uid] sc.internal_ports
  then type_error (loc id)
       (fun ppf ->
          fprintf ppf
          ("@[cannot@ rebind@ port@ name@ (party@ name@ of@ " ^^
           "functionality)@ in@ pattern@]"))
  else {sc with
          consts = IdMap.add uid typ sc.consts}

(* pattern matching *)

let check_port_var_binding
    (abip : all_basic_inter_paths) (idp : string list)
    (vid : id) (sc : state_context) : state_context = 
  let d = List.exists (fun bp -> fst bp = idp) abip.direct in
  let is_sim = List.mem "simulator" sc.flags in
  if not d
  then type_error (loc vid)
       (fun ppf ->
          fprintf ppf
          (if is_sim
           then ("@[message@ patterns@ matching@ adversarial@ messages@ " ^^
                 "may@ not@ bind@ source@ ports@ to@ identifiers")
           else ("@[message@ patterns@ matching@ adversarial@ and@ " ^^
                 "internal@ messages@ may@ not@ bind@ source@ ports@ " ^^
                 "to@ identifiers@]")))
  else check_add_const vid port_type sc

let check_non_port_var_binding
    (abip : all_basic_inter_paths) (idp : string list) (mppl : EcLocation.t)
      : unit = 
  let d = List.exists (fun bp -> fst bp = idp) abip.direct in
  if d
  then type_error mppl
       (fun ppf ->
          fprintf ppf
          ("@[non-\"*\"@ message@ patterns@ matching@ messages@ of@ direct@ " ^^
           "interfaces@ implemented@ by@ functionalities@ must@ bind@ " ^^
           "source@ ports@ to@ identifiers@]"))
  else ()

let check_pat_add_const
    (sc : state_context) (pat : pat) (typ : typ) : state_context = 
  match pat with
  | PatWildcard _ -> sc
  | PatId id      -> check_add_const id typ sc

let rec get_loc_ty (ty : ty) : EcLocation.t = 
  match ty with
  | NamedTy id -> loc id
  | TupleTy tl -> mergeall (List.map (fun t -> get_loc_ty t) tl)

let get_loc_pat (pat : pat) : EcLocation.t = 
  match pat with
  | PatWildcard l -> l
  | PatId id      -> loc id

let get_loc_pat_list (tm : pat list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_pat mi) tm)

let ids_of_pat (pat : pat) : IdSet.t =
  match pat with
  | PatWildcard _ -> IdSet.empty
  | PatId id      -> IdSet.singleton (unloc id)

let ids_of_pats (pats : pat list) : IdSet.t =
  List.fold_left
  (fun uids pat -> IdSet.union uids (ids_of_pat pat))
  IdSet.empty pats

(* TODO: once we have tuple patterns, need to check for disjointness
   of identifer binding *)

let check_disjoint_bindings (pats : pat list) : unit =
  ignore
  (List.fold_left
   (fun uids pat ->
      let pat_uids = ids_of_pat pat in
      let com_uids = IdSet.inter uids pat_uids in
      if IdSet.is_empty com_uids
      then IdSet.union uids pat_uids
      else let ex_com = IdSet.choose com_uids in
           type_error (get_loc_pat_list pats)
           (fun ppf ->
              fprintf ppf "@[pattern@ binds@ %s@ more@ than@ once@]" ex_com))
   IdSet.empty pats)

let check_pat_args_with_msg_type
    (bips : basic_inter_path list) (mp : string list * string)
    (pats : pat list) (sc : state_context) : state_context = 
  let bip = List.find (fun p -> fst p = fst mp) bips in
  let mtyp =
    indexed_map_to_list
    (unlocm ((unloc (IdMap.find (snd mp) (snd bip))).params_map)) in
  let () =
    if List.length mtyp <> List.length pats
    then type_error (get_loc_pat_list pats)
         (fun ppf ->
            fprintf ppf
            ("@[the@ number@ of@ argument@ patterns@ is@ different@ " ^^
             "from@ the@ number@ of@ message@ parameters@]")) in
  let () = check_disjoint_bindings pats in
  List.fold_left2 check_pat_add_const sc pats mtyp

let check_missing_pat_args_with_msg_type
    (bips : basic_inter_path list) (mp : string list * string)
    (l : EcLocation.t) : unit = 
  let bip = List.find (fun p -> fst p = fst mp) bips in
  let mtyp =
    indexed_map_to_list
    (unlocm ((unloc (IdMap.find (snd mp) (snd bip))).params_map)) in
  if List.length mtyp <> 0
  then type_error l
         (fun ppf ->
            fprintf ppf
            ("@[the@ number@ of@ argument@ patterns@ is@ different@ " ^^
             "from@ the@ number@ of@ message@ parameters@]"))

let check_pat_args
    (bips : basic_inter_path list) (msg_pat : msg_pat)
    (sc : state_context) : state_context = 
  match msg_pat.pat_args with
  | None      ->
      let () =
        match msg_pat.msg_path_pat.msg_or_star with
        | MsgOrStarStar _ -> ()
        | MsgOrStarMsg id ->
            check_missing_pat_args_with_msg_type bips
            (unlocs msg_pat.msg_path_pat.inter_id_path, unloc id) (loc id) in
      sc
  | Some pats -> 
      (match msg_pat.msg_path_pat.msg_or_star with
       | MsgOrStarStar _ -> failure "cannot happen - check in parser"
       | MsgOrStarMsg id ->
           check_pat_args_with_msg_type bips
           (unlocs msg_pat.msg_path_pat.inter_id_path, unloc id) pats sc)

let check_msg_pat
    (abip : all_basic_inter_paths) (msg_pat : msg_pat)
    (sc : state_context) : state_context = 
  let abip = incoming_abip abip in
  let () = check_msg_path_pat abip sc msg_pat.msg_path_pat in
  let sv' =        
    match msg_pat.port_id with
    | Some id ->
        (* we know msg_pat.msg_path_pat does not end in "*" *)
        let () =
          let uids_pat_args = ids_of_pats (msg_pat.pat_args |? []) in
          if IdSet.mem (unloc id) uids_pat_args
          then type_error (loc id)
               (fun ppf ->
                  fprintf ppf
                  ("@[source@ port@ of@ message@ pattern@ is@ also@ bound@ " ^^
                   "in@ message@ argument@ patterns@]")) in
        check_port_var_binding abip
        (unlocs msg_pat.msg_path_pat.inter_id_path) id sc
    | None    ->
        if msg_path_pat_ends_star msg_pat.msg_path_pat
        then sc
        else let mppl = msg_path_pat_loc msg_pat.msg_path_pat in
             (check_non_port_var_binding abip 
              (unlocs msg_pat.msg_path_pat.inter_id_path) mppl;
              sc) in
  let bips = flatten_all_basic_inter_paths abip in
  check_pat_args bips msg_pat sv'

(* checking instructions *)

let get_var_type (sc : state_context) (id : id) : typ = 
  let vs =
    IdMap.union
    (fun _ _ ->
       failure
       ("Impossible! we already checked that params and " ^
        "vars have different names"))
    sc.consts sc.vars in
  IdMap.find (unloc id) vs

let check_initialized
    (sc : state_context) (sa : state_analysis) (id : id) : unit = 
  let uid = unloc id in
  if IdMap.mem uid sc.consts || IdSet.mem uid sa.initialized_vs then ()
  else type_error (loc id)
       (fun ppf -> fprintf ppf "@[%s@ may@ not@ be@ initialized@]" uid)

let check_expr_var
    (sc : state_context) (sa : state_analysis) (id : id) : typ = 
  let r = get_var_type sc id in
  let () = check_initialized sc sa id in
  r

let check_is_internal_port (sc : state_context) (qid : qid) : bool =
  QidSet.mem (unlocs qid) sc.internal_ports

let check_qid_type
    (sc : state_context) (sa : state_analysis) (qid : qid) : typ = 
  try
    (match qid with
     | id :: [] -> check_expr_var sc sa id
     | _        -> raise Not_found)
  with
  | Not_found -> 
      if check_is_internal_port sc qid then port_type else raise Not_found

let check_expression
    (sc : state_context) (sa : state_analysis) (expr : expression) : typ = 
  UcExpressions.check_expression (check_qid_type sc sa) expr

let check_val_assign
    (sc : state_context) (sa : state_analysis)
    (vid : id) (ex : expression) : state_analysis = 
  let etyp = check_expression sc sa ex in
  check_assign_core vid etyp sc sa

let check_sampl_assign
    (sc : state_context) (sa : state_analysis)
    (vid : id) (ex : expression) : state_analysis =
  let etyp = check_expression sc sa ex in
  if not (UcExpressions.is_distribution etyp)
  then type_error (loc ex)
       (fun ppf ->
          fprintf ppf
          "@[you@ can@ sample@ only@ from@ distributions@]")
  else let dtyp = UcExpressions.get_distribution_typ etyp in 
       check_assign_core vid dtyp sc sa

let check_state_expr
    (se : state_expr) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) : unit = 
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
          let et = check_expression sc sa sip in
          if sigt <> et
          then type_error (loc sip)
               (fun ppf ->
                  fprintf ppf
                  ("@[parameter@ %d@ of@ state@ %s@ has@ type@ %a,@ " ^^
                   "which@ is@ incompatible@ with@ type@ %a@ " ^^
                   "of@ corresponding@ argument@]")
                   (i + 1) (unloc se.id) format_typ sigt format_typ et))
       te

let check_msg_arguments
    (mp : msg_path) (es : expression list located) (mc : typ_index IdMap.t)
    (sc : state_context) (sa : state_analysis) : unit = 
  let sg = indexed_map_to_list (unlocm mc) in
  if List.length (unloc es) <> List.length sg
  then type_error (loc es)
       (fun ppf ->
          fprintf ppf "@[wrong@ number@ of@ message@ arguments@]")
  else List.iter2i
       (fun i ex typ ->
          let tex = check_expression sc sa ex in
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
    (msg : msg_expr) (param_tis : typ_index IdMap.t) (sc : state_context)
    (sa : state_analysis) : unit = 
  let l = msg_path_loc msg.path in
  let () =
    match msg.port_id with
    | Some pid ->
        (check_declared_with_compatible_type pid port_type sc;
         check_initialized sc sa pid)
    | None   ->
        type_error l
        (fun ppf ->
           fprintf ppf
           ("@[outgoing@ messages@ to@ sub-interfaces@ of@ composite@ " ^^
            "direct@ interfaces@ must@ have@ destination@ ports@]")) in
  check_msg_arguments msg.path msg.args param_tis sc sa

let check_send_adversarial
    (msg : msg_expr) (param_tis : typ_index IdMap.t) (sc : state_context)
    (sa : state_analysis) : unit = 
  let () =
    match msg.port_id with
    | Some pid ->
        type_error (loc pid)
        (fun ppf ->
           fprintf ppf
           "@[adversarial@ messages@ must@ not@ have@ destination@ ports@]")
    | None     -> () in
  check_msg_arguments msg.path msg.args param_tis sc sa

let check_send_internal
    (msg : msg_expr) (param_tis : typ_index IdMap.t)
    (sc : state_context) (sa : state_analysis) : unit = 
  let () =
    match msg.port_id with
    | Some pid ->
        type_error (loc pid)
        (fun ppf ->
           fprintf ppf
           ("@[messages@ to@ subfunctionalities@ must@ not@ have@ " ^^
            "destination@ ports@]"))
    | None     -> () in
  check_msg_arguments msg.path msg.args param_tis sc sa

let is_msg_path_in_basic_inter_paths
    (mp : msg_path) (bips : basic_inter_path list) : bool = 
  let bipo =
    List.find_opt (fun bip -> fst bip = unlocs mp.inter_id_path) bips in
  Option.is_some bipo

let get_msg_def_for_msg_path
    (mp : msg_path) (bips : basic_inter_path list) : message_def_body_tyd = 
  let iip = unlocs mp.inter_id_path in
  let bip = List.find (fun bip -> fst bip = iip) bips in
  let umid = unloc mp.msg in
  let mdb = IdMap.find umid (snd bip) in
  unloc mdb

let check_send_msg_path
    (msg : msg_expr) (abip : all_basic_inter_paths) : unit =
  let abip = outgoing_abip abip in
  check_outgoing_msg_path abip msg.path

let check_msg_expr
    (msg : msg_expr) (abip : all_basic_inter_paths)
    (sc : state_context) (sa : state_analysis) : unit = 
  let () = check_send_msg_path msg abip in
  let bips = abip.direct @ abip.adversarial @ abip.internal in
  let param_tis = (get_msg_def_for_msg_path msg.path bips).params_map in
  if is_msg_path_in_basic_inter_paths msg.path abip.direct
    then check_send_direct msg param_tis sc sa
  else if is_msg_path_in_basic_inter_paths msg.path abip.adversarial
    then check_send_adversarial msg param_tis sc sa
  else if is_msg_path_in_basic_inter_paths msg.path abip.internal
    then check_send_internal msg param_tis sc sa
  else failure "impossible - will be one of above"

let check_send_and_transition
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sat : send_and_transition) (sc : state_context) (sa : state_analysis)
      : unit = 
  let () = check_msg_expr sat.msg_expr abip sc sa in
  check_state_expr sat.state_expr ss sc sa

let merge_state_analysis (sa1 : state_analysis) (sa2 : state_analysis)
      : state_analysis = 
  {initialized_vs = IdSet.inter sa1.initialized_vs sa2.initialized_vs}

let rec check_ite
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis)
    (ex : expression) (tins : instruction list located)
    (eins : instruction list located option)
      : state_analysis = 
  if check_expression sc sa ex <> bool_type
  then type_error (loc ex)
       (fun ppf ->
          fprintf ppf
          "@[the@ condition@ must@ be@ a@ boolean expression@]")
  else check_branches abip ss sc sc sa tins eins

and check_branches
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc1 : state_context) (sc2 : state_context) (sa : state_analysis)
    (ins1 : instruction list located)
    (ins2 : instruction list located option)
      : state_analysis = 
  let sa1 = check_instructions abip ss sc1 sa ins1 in
  let sa2 =
    match ins2 with                         
    | Some is -> check_instructions abip ss sc2 sa is
    | None    -> sa in
  merge_state_analysis sa1 sa2

and check_decode
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis)
    (ex : expression) (ty : ty)
    (pats : pat list) (okins : instruction list located)
    (erins : instruction list located)
      : state_analysis = 
  let () =
    if check_expression sc sa ex <> univ_type
    then type_error (loc ex)
         (fun ppf ->
            fprintf ppf
            "@[only@ expressions@ of@ univ@ type@ can@ be@ decoded@]") in
  let dt =
    match check_type ty with
    | Tconstr (x, y) -> [Tconstr (x, y)]
    | Ttuple  t      -> t
    | _              ->
        failure
        "check_type is supposed to return only Tconstr or Ttuple" in
  let () =
    if List.length pats <> List.length dt
    then type_error (get_loc_pat_list pats)
         (fun ppf ->
            fprintf ppf
            ("@[the@ number@ of@ bindings@ is@ different@ from@ the@ " ^^
             "arity@ of@ decoded@ type@]")) in
  let () = check_disjoint_bindings pats in
  let sc' = List.fold_left2 check_pat_add_const sc pats dt in
  check_branches abip ss sc' sc sa okins (Some erins)

and check_instruction
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis) (i : instruction)
      : state_analysis = 
  match unloc i with
  | Assign (vid, ex)                    -> check_val_assign sc sa vid ex
  | Sample (vid, ex)                    -> check_sampl_assign sc sa vid ex
  | ITE (ex, tins, eins)                -> check_ite abip ss sc sa ex tins eins
  | Decode (ex, ty, ok_pats, okins, erins) ->
      check_decode abip ss sc sa ex ty ok_pats okins erins
  | SendAndTransition sat               ->
      (check_send_and_transition abip ss sat sc sa; sa)
  | Fail                                -> sa

and check_instructions
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis)
    (is : instruction list located)
      : state_analysis = 
  let uis = unloc is in
  List.fold_left (check_instruction abip ss sc) sa uis

(* checking where control transfer instructions (send-and-transition and
   fail) may appear *)

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

let rec check_instrs_transfer_at_end (is : instruction list located) : unit =
  let uis = unloc is in
  match uis with
  | [] -> failure_to_transfer_control (loc is)
  | is ->
      let xs = List.take (List.length is - 1) is in
      (List.iter check_instr_not_transfer xs;
       check_instr_end_in_transfer (List.last is))

and check_instrs_not_transfer (is : instruction list located) : unit =
  let uis = unloc is in
  List.iter check_instr_not_transfer uis

and check_instr_end_in_transfer (instr : instruction) : unit =
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

and check_instr_not_transfer (instr : instruction) : unit =
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

(* checking message match clauses *)

let check_msg_match_code
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis)
    (is : instruction list located)
      : unit = 
  let () = ignore (check_instructions abip ss sc sa is) in
  check_instrs_transfer_at_end is

let check_msg_match_clause
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis)
    (mmc : msg_match_clause) : unit = 
  let sc' = check_msg_pat abip mmc.msg_pat sc in
  check_msg_match_code abip ss sc' sa mmc.code

(* checking states *)

let check_state_code
    (abip : all_basic_inter_paths) (ss : state_sig IdMap.t)
    (sc : state_context) (sa : state_analysis)
    (mmclauses : msg_match_clause list)
      : unit =
  let () =
    List.iter
    (fun mmc -> check_msg_match_clause abip ss sc sa mmc)
    mmclauses in
  check_coverage_msg_path_pats abip sc
  (List.map (fun mmc -> mmc.msg_pat) mmclauses)

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

(* check the top-level of a state_def *)

let check_toplevel_state
    (init_id : id) (internal_ports : QidSet.t) (st : state) : state_tyd = 
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
  let () =
    let dup =
      IdMap.find_first_opt
      (fun param -> QidSet.mem [param] internal_ports)
      params in
    match dup with
    | None              -> ()
    | Some (param, typ) ->
        type_error (loc typ)
        (fun ppf ->
           fprintf ppf
           ("@[parameter@ name@ %s@ is@ the@ same@ as@ one@ of@ the@ " ^^
            "functionality's@ internal@ ports@ (party@ names)@]")
           param) in
  let () =
    let dup =
      IdMap.find_first_opt (fun var -> IdMap.mem var params) vars in
    match dup with
    | None            -> ()
    | Some (var, typ) ->
        type_error (loc typ)
        (fun ppf ->
           fprintf ppf
           ("@[variable@ name@ %s@ is@ the@ same@ as@ one@ of@ the@ " ^^
            "state's@ parameters@]")
           var) in
  let () =
    let dup =
      IdMap.find_first_opt (fun var -> QidSet.mem [var] internal_ports) vars in
    match dup with
    | None              -> ()
    | Some (param, typ) ->
        type_error (loc typ)
        (fun ppf ->
           fprintf ppf
           ("@[variable@ name@ %s@ is@ the@ same@ as@ one@ of@ the@ " ^^
            "functionality's@ internal@ ports@ (party@ names)@]")
           param) in
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

let check_toplevel_states
    (id : id) (internal_ports : QidSet.t) (state_defs : state_def list)
      : state_tyd IdMap.t = 
  let init_id = check_exactly_one_initial_state id state_defs in
  let states = List.map (fun sd -> drop_state_construct sd) state_defs in
  let state_map =
    check_unique_ids
    (fun ppf -> fprintf ppf "@[duplicate@ state@ name@]")
    states (fun s -> s.id) in
  IdMap.map (check_toplevel_state init_id internal_ports) state_map 

(* check the lower-level of an individual state_tyd *)

let check_lowlevel_state
    (abip : all_basic_inter_paths) (flags : string list)
    (internal_ports : QidSet.t) (states : state_tyd IdMap.t) 
    (state : state_tyd) : unit = 
  let us = unloc state in
  let sc = init_state_context (unloc state) internal_ports flags in
  let sa = init_state_analysis in
  let ss = get_state_sigs states in
  check_state_code abip ss sc sa us.mmclauses

(* check the lower-level of a state_tyd IdMap.t state machine *)

let check_lowlevel_states
    (abip : all_basic_inter_paths) (flags : string list)
    (internal_ports : QidSet.t) (states : state_tyd IdMap.t)
      : unit = 
  IdMap.iter
  (fun _ -> check_lowlevel_state abip flags internal_ports states)
  states

(* this is for use in checking ideal functionalities and simulators;
   not used when checking parties of real functionalities *)

let check_states
    (id : id) (abip : all_basic_inter_paths) (flags : string list)
    (internal_ports : QidSet.t) (state_defs : state_def list)
      : state_tyd IdMap.t =
  let states = check_toplevel_states id internal_ports state_defs in
  let () =
    check_lowlevel_states abip flags internal_ports states in
  states

(**************************** functionality checks ****************************)

let filter_basic_inter_paths_by_serves
    (bips : basic_inter_path list) (serves : string list located list)
      : basic_inter_path list = 
  List.filter
  (fun bip -> List.exists (fun serv -> unloc serv = fst bip) serves)
  bips

let get_all_external_basic_inter_paths
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (dirid : string) (advid : string option)
      : all_basic_inter_paths = 
  let direct = get_basic_inter_paths_from_inter_id dirid dir_inter_map in
  let adversarial = 
    match advid with
    | Some id -> get_basic_inter_paths_from_inter_id id adv_inter_map
    | None    -> [] in
  {direct = direct; adversarial = adversarial; internal = []}

let get_dir_inter_id_impl_by_fun_id
    (funid : string) (fun_map : fun_tyd IdMap.t) : string = 
  let func = IdMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr  -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

(* does *not* take a real_fun_body_tyd or fun_body_tyd as a parameter,
   because we need to call function before these are constructed; but
   *does* take some components of real_fun_body_tyd *)

let get_all_basic_inter_paths_of_real_fun_party
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (fun_map : fun_tyd IdMap.t) (dirid : string) (advid : string option)
    (params : (id * int) IdMap.t) (sub_funs : id IdMap.t)
    (serves : string list located list) : all_basic_inter_paths = 
  let abips =
    get_all_external_basic_inter_paths
    dir_inter_map adv_inter_map dirid advid in
  let dir_bips =
    filter_basic_inter_paths_by_serves abips.direct serves in
  let adv_bips =
    filter_basic_inter_paths_by_serves abips.adversarial serves in
  let param_bips_map =
    IdMap.mapi
    (fun pid p -> 
       let dirid = unloc (fst p) in
       get_basic_inter_paths pid dirid dir_inter_map)
    params in
  let sub_fun_bips_map =
    IdMap.mapi
    (fun sfid (sf : id) ->
       let dirid = get_dir_inter_id_impl_by_fun_id (unloc sf) fun_map in
       get_basic_inter_paths sfid dirid dir_inter_map)
    sub_funs in
  let internal_bips_map =
    IdMap.union
    (fun _ _ _ -> failure "impossible - params and subfuns disjoint")
    param_bips_map sub_fun_bips_map in
  let internal = IdMap.fold (fun _ bips l -> l @ bips) internal_bips_map [] in
  {direct = dir_bips; adversarial = adv_bips; internal = internal}

let check_toplevel_party
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (id_dir_inter : string) (id_adv_inter : string option)
    (internal_ports : QidSet.t) (pd : party_def) : party_def_tyd = 
  let serves =
    List.map
    (check_inter_id_path id_dir_inter id_adv_inter dir_inter_map adv_inter_map)
    pd.serves in
  let () = check_served_inter_id_paths serves id_dir_inter pd.id in
  let states =
    check_toplevel_states pd.id internal_ports pd.states in
  mk_loc (loc pd.id) {serves = serves; states = states}

let check_toplevel_parties
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (id_dir_inter : string) (id_adv_inter : string option)
    (internal_ports : QidSet.t) (party_defs : party_def IdMap.t)
      : party_def_tyd IdMap.t =
  let parties =
    IdMap.map
    (check_toplevel_party dir_inter_map adv_inter_map id_dir_inter id_adv_inter
     internal_ports)
    party_defs in
  let () =
    check_parties_serve_coverage_and_distinct parties id_dir_inter id_adv_inter
    dir_inter_map adv_inter_map in
  parties

let check_lowlevel_party
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (fun_map : fun_tyd IdMap.t) (id_dir_inter : string)
    (id_adv_inter : string option) (internal_ports : QidSet.t)
    (params : (id * int) IdMap.t) (sub_funs : id IdMap.t)
    (pdt : party_def_tyd) : unit = 
  let updt = unloc pdt in
  let abip =
    get_all_basic_inter_paths_of_real_fun_party
    dir_inter_map adv_inter_map fun_map id_dir_inter id_adv_inter
    params sub_funs updt.serves in
  check_lowlevel_states abip [] internal_ports updt.states

let check_parties
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (fun_map : fun_tyd IdMap.t) (id_dir_inter : string)
    (id_adv_inter : string option) (params : (id * int) IdMap.t)
    (sub_funs : id IdMap.t) (party_defs : party_def IdMap.t)
      : party_def_tyd IdMap.t = 
  let internal_ports = get_keys_as_sing_qids party_defs in
  let parties =
    check_toplevel_parties dir_inter_map adv_inter_map id_dir_inter id_adv_inter
    internal_ports party_defs in
  let () =
    IdMap.iter
    (fun _ ->
       check_lowlevel_party dir_inter_map adv_inter_map fun_map
       id_dir_inter id_adv_inter internal_ports params sub_funs)
    parties in
  parties

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

let check_fun (maps : maps_tyd) (fund : fun_def) : fun_tyd =
  let () = check_exists_inter DirectInterKind maps.dir_inter_map fund.id_dir in
  let () = check_is_composite DirectInterKind maps.dir_inter_map fund.id_dir in
  let uid_dir_inter = unloc fund.id_dir in 
  let uid_adv_inter =
    match fund.id_adv with
    | None    -> None
    | Some id -> 
        (check_exists_inter AdversarialInterKind maps.adv_inter_map id;
         Some (unloc id)) in
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
        fbr.party_defs (fun x -> x.id) in
      let parties =
        check_parties maps.dir_inter_map maps.adv_inter_map maps.fun_map
        uid_dir_inter uid_adv_inter params sub_funs party_defs in
      let fbrt =
        {params = params; id_dir_inter = uid_dir_inter;
         id_adv_inter = uid_adv_inter; sub_funs = sub_funs;
         parties = parties} in
      let funbody = FunBodyRealTyd fbrt in
      mk_loc (loc fund.id) funbody
  | FunBodyIdeal state_defs ->
      let () =
        match fund.id_adv with
        | None ->
            type_error (loc fund.id)
            (fun ppf ->
               fprintf ppf
               ("@[an@ ideal@ functionality@ must@ implement@ a@ basic@ " ^^
                "adversarial@ interface@]"))
        | Some id ->
            (check_exists_inter AdversarialInterKind maps.adv_inter_map id;
             check_is_basic AdversarialInterKind maps.adv_inter_map id) in
      let abip =
        get_all_external_basic_inter_paths maps.dir_inter_map maps.adv_inter_map
        uid_dir_inter uid_adv_inter in
      let states = check_states fund.id abip [] QidSet.empty state_defs in
      let ifbt =
        {id_dir_inter = uid_dir_inter; id_adv_inter = Option.get uid_adv_inter;
         states = states} in
      let funbody = FunBodyIdealTyd ifbt in
      mk_loc (loc fund.id) funbody

let check_fun_def (maps : maps_tyd) (fund : fun_def) : maps_tyd =
  let uid = unloc fund.id in
  let () =
    if exists_id_maps_tyd maps uid
    then type_error (loc fund.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let funt = check_fun maps fund in
  {maps with
     fun_map = IdMap.add uid funt maps.fun_map}

(****************************** simulator checks ******************************)

let get_sim_components
    (fun_map : fun_tyd IdMap.t) (sims : string)
    (sim_real_fun_arg_uids : string list) : fun_body_tyd QidMap.t = 
  let sims_body = unloc (IdMap.find sims fun_map) in
  let qidmap_fun = QidMap.singleton [sims] sims_body in
  let qidmap_params =
    let pids =
      IdMap.fold
      (fun pid _ pids -> pid :: pids)
      (real_fun_body_tyd_of sims_body).params [] in
    List.fold_left2
    (fun mp pid aid ->
       let a_body = unloc (IdMap.find aid fun_map) in
       QidMap.add [sims; pid] a_body mp)
    QidMap.empty pids sim_real_fun_arg_uids in
  let qidmap_subfuns =
    IdMap.fold
    (fun sfid ideal_fun_id mp ->
       let ideal_body = unloc (IdMap.find (unloc ideal_fun_id) fun_map) in
       QidMap.add [sims; sfid] ideal_body mp)
    (real_fun_body_tyd_of sims_body).sub_funs QidMap.empty in
  let disj = (fun _ _ _ -> failure "cannot happen") in
  QidMap.union disj qidmap_fun (QidMap.union disj qidmap_params qidmap_subfuns)
                
let get_fun_adv_basic_inter_paths
    (adv_inter_map : inter_tyd IdMap.t) (fun_body : fun_body_tyd)
      : basic_inter_path list = 
  match id_adv_inter_of_fun_body_tyd fun_body with
  | Some id -> get_basic_inter_paths_from_inter_id id adv_inter_map 
  | None    -> []

let get_sim_basic_inter_id_paths
    (adv_inter_map : inter_tyd IdMap.t) (uses : string)
    (comps : fun_body_tyd QidMap.t) : basic_inter_path list = 
  let bips_comps_map =
    QidMap.map (get_fun_adv_basic_inter_paths adv_inter_map) comps in
  let bips_map =
    QidMap.add
    []
    (List.map invert_basic_inter_path
     (get_basic_inter_paths_from_inter_id uses adv_inter_map))
    bips_comps_map in
  QidMap.fold
  (fun qid bips_of_qid bips ->
     bips @ List.map (fun bip -> (qid @ fst bip, snd bip)) bips_of_qid)
  bips_map []

let get_internal_ports (real_fun_body : real_fun_body_tyd) : QidSet.t = 
  get_keys_as_sing_qids real_fun_body.parties

let get_sim_internal_ports
    (fun_map : fun_tyd IdMap.t) (sims : string) : QidSet.t = 
  let sims_fbt = real_fun_body_tyd_of (unloc (IdMap.find sims fun_map)) in
  let int_ports = get_internal_ports sims_fbt in
  QidSet.map (fun qid -> sims :: qid) int_ports
        
let check_exists_fun (funs : fun_tyd IdMap.t) (funid : id) = 
  let ufid = unloc funid in
  if exists_id funs ufid then ()
  else type_error (loc funid)
       (fun ppf -> fprintf ppf "@[functionality@ isn't@ defined:@ %s@]" ufid)

let check_exists_and_is_real_fun (funs : fun_tyd IdMap.t) (funid : id) = 
  let () = check_exists_fun funs funid in
  let f = unloc (IdMap.find (unloc funid) funs) in
  if not (is_real_fun_body_tyd f)
  then type_error (loc funid)
       (fun ppf ->
          fprintf ppf
          "@[the@ simulated@ functionality@ must@ be@ a@ real@ functionality@]")

let get_params_of_real_fun_id
    (fun_map : fun_tyd IdMap.t) (funid : string) : string list = 
  let func = IdMap.find funid fun_map in
  match unloc func with
  | FunBodyRealTyd fbr -> unlocs (indexed_map_to_list fbr.params)
  | FunBodyIdealTyd _  -> failure "cannot happen - will be real functionality"

let check_sim_fun_args
    (funs : fun_tyd IdMap.t) (real_fun_id : id)
    (args : id list located) : unit =
  let dir_id_params = get_params_of_real_fun_id funs (unloc real_fun_id) in
  let dir_id_args =
    List.map
    (fun id -> get_dir_inter_id_impl_by_fun_id id funs)
    (unlocs (unloc args)) in
  let () =
    if List.length dir_id_params <> List.length dir_id_args
    then type_error (loc args)
         (fun ppf ->
            fprintf ppf
            "@[wrong@ number@ of@ arguments@ for@ functionality@]")
    else List.iteri
         (fun i pid ->
            if List.nth dir_id_params i <> List.nth dir_id_args i
            then type_error (loc pid)
                 (fun ppf ->
                    fprintf ppf
                    ("@[argument@ %d@ implements@ composite@ direct@ " ^^
                     "interface@ %s,@ whereas@ it@ should@ implement@ %s@]")
                    (i + 1) (List.nth dir_id_args i)
                    (List.nth dir_id_params i)))
         (unloc args) in
  List.iter
  (fun pid ->
     let funb = unloc (IdMap.find (unloc pid) funs) in
     match funb with
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
  (unloc args)

let check_sim
    (adv_inter_map : inter_tyd IdMap.t) (fun_map : fun_tyd IdMap.t)
    (sd : sim_def) : sim_def_tyd = 
  let () = check_exists_inter AdversarialInterKind adv_inter_map sd.uses in
  let () = check_is_basic AdversarialInterKind adv_inter_map sd.uses in
  let uses = unloc sd.uses in
  let () = check_exists_and_is_real_fun fun_map sd.sims in
  let sims = unloc sd.sims in
  let () = List.iter (check_exists_fun fun_map) (unloc sd.sims_arg_ids) in
  let () = check_sim_fun_args fun_map sd.sims sd.sims_arg_ids in
  let sims_arg_ids = unlocs (unloc sd.sims_arg_ids) in
  let internal_ports = get_sim_internal_ports fun_map sims in
  let comps = get_sim_components fun_map sims sims_arg_ids in
  let bips = get_sim_basic_inter_id_paths adv_inter_map uses comps in
  let abip = {direct = []; adversarial = bips; internal = []} in
  let states = check_states sd.id abip ["simulator"] internal_ports sd.states in
  let sbt =
    {uses = uses; sims = sims; sims_arg_ids = sims_arg_ids; states = states} in
  mk_loc (loc sd.id) sbt

let check_sim_def (maps : maps_tyd) (simd : sim_def) : maps_tyd =
  let uid = unloc simd.id in
  let () =
    if exists_id_maps_tyd maps uid
    then type_error (loc simd.id)
         (fun ppf ->
            fprintf ppf
            "@[identifier@ already@ declared@ at@ top-level:@ %s@]" uid) in
  let sdt = check_sim maps.adv_inter_map maps.fun_map simd in
  {maps with sim_map = IdMap.add uid sdt maps.sim_map}
*)
(***************************** definition checks ******************************)

let partition_maps qual_file maps =
  let part_dir_inter_map =
    IdMap.partition 
    (fun _ v -> filename_of_loc (loc v) = qual_file)
    maps.dir_inter_map in
  let part_adv_inter_map =
    IdMap.partition 
    (fun _ v -> filename_of_loc (loc v) = qual_file)
    maps.adv_inter_map in
  let part_fun_map =
    IdMap.partition 
    (fun _ v -> filename_of_loc (loc v) = qual_file)
    maps.fun_map in
  let part_sim_map =
    IdMap.partition 
    (fun _ v -> filename_of_loc (loc v) = qual_file)
    maps.sim_map in
  {required_maps =
     {dir_inter_map = snd part_dir_inter_map;
      adv_inter_map = snd part_adv_inter_map;
      fun_map       = snd part_fun_map;
      sim_map       = snd part_sim_map};
   current_maps  =
     {dir_inter_map = fst part_dir_inter_map;
      adv_inter_map = fst part_adv_inter_map;
      fun_map       = fst part_fun_map;
      sim_map       = fst part_sim_map}}

let check_defs qual_file maps defs = 
  let check_def maps def =
    match def with
    | InterDef interd -> check_inter_def maps interd
    | _ -> maps
 (*   | FunDef fund     -> check_fun_def maps fund
    | SimDef simd     -> check_sim_def maps simd *)in
  let maps = List.fold_left check_def maps defs in
  partition_maps qual_file maps

(**************************** specification checks ****************************)

let union_maps id map_old map_new =
  let conflict l file uid =
    type_error l
    (fun ppf ->
       fprintf ppf
       ("@[when@ requiring@ UC@ file@ %s,@ definition@ of@ %s@ " ^^
        "conflicts@ with@ definition@ from@ previous@ require@]")
       file uid) in
  let check_same_loc k l1 l2 =
    if l1 <> l2
    then conflict (loc id) (unloc id) k in
  let check_disjoint_maps maps =
    let ks =
      List.map fst
      (IdMap.bindings (IdMap.mapi (fun k _ -> k) maps.dir_inter_map) @
       IdMap.bindings (IdMap.mapi (fun k _ -> k) maps.adv_inter_map) @
       IdMap.bindings (IdMap.mapi (fun k _ -> k) maps.fun_map) @
       IdMap.bindings (IdMap.mapi (fun k _ -> k) maps.sim_map)) in
    match find_dup ks with
    | None   -> ()
    | Some k -> conflict (loc id) (unloc id) k in
  let maps =
    {dir_inter_map =
       IdMap.union
       (fun k v1 v2 -> check_same_loc k (loc v1) (loc v2); Some v1)
       map_old.dir_inter_map map_new.dir_inter_map;
     adv_inter_map =
       IdMap.union
       (fun k v1 v2 -> check_same_loc k (loc v1) (loc v2); Some v1)
       map_old.adv_inter_map map_new.adv_inter_map;
     fun_map =
       IdMap.union
       (fun k v1 v2 -> check_same_loc k (loc v1) (loc v2); Some v1)
       map_old.fun_map map_new.fun_map;
     sim_map =
       IdMap.union
       (fun k v1 v2 -> check_same_loc k (loc v1) (loc v2); Some v1)
       map_old.sim_map map_new.sim_map} in
  let () = check_disjoint_maps maps in
  maps

let load_uc_req check_id maps id =
  let uid = unloc id in
  if not (Char.is_uppercase uid.[0])
  then type_error (loc id)
       (fun ppf ->
          fprintf ppf
          ("@[UC@ (.uc)@ file@ to@ be@ required@ must@ begin@ " ^^
           "with@ uppercase@ letter:@ %s@]")
          uid)
  else let () = EcCommands.ucdsl_new () in
       let tyspec = check_id id in
       let maps' =
         union_maps id tyspec.required_maps tyspec.current_maps in
       let maps = union_maps id maps maps' in
       let () = EcCommands.ucdsl_end () in
       maps

let load_uc_reqs check_id maps reqs = 
  List.fold_left (load_uc_req check_id) maps reqs

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
    try UcEcInterface.require id (Some `Import) with
    | Failure f ->
        type_error (loc id)
        (fun ppf ->
           fprintf ppf
           "@[error@ when@ importing@ EasyCrypt@ theory@ %s:@ \"%s\"@]"
           (unloc id) f) in
  List.iter reqimp reqs

let typecheck (qual_file : string) (check_id : psymbol -> typed_spec)
              (spec : spec) : typed_spec =
  let empty_maps =
    {dir_inter_map = IdMap.empty;
     adv_inter_map = IdMap.empty;
     fun_map       = IdMap.empty;
     sim_map       = IdMap.empty} in
  let maps = load_uc_reqs check_id empty_maps spec.externals.uc_requires in
  let () = load_ec_reqs spec.externals.ec_requires in
  try ignore (check_defs qual_file maps spec.definitions);
      failure "disconnected!" with
  | EcTyping.TyError (l, env, tyerr) ->
      type_error l
      (fun ppf -> UcEcUserMessages.TypingError.pp_tyerror env ppf tyerr)
