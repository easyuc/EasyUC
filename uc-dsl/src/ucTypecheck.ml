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

(* circular references *)

let refs_refs (get_refs : string -> IdSet.t)  (refs : IdSet.t) : IdSet.t = 
  let add_refs elt set = IdSet.union (get_refs elt) set in
  IdSet.fold add_refs refs IdSet.empty

let get_dependencies (get_refs : string -> IdSet.t) (id : string)  = 
  let rec tc refs = 
    let refs' = refs_refs get_refs refs in
    if IdSet.subset refs' refs then refs
    else tc (IdSet.union refs' refs)
  in tc (get_refs id)

let check_circ_refs (get_refs : ('o located) IdMap.t -> string -> IdSet.t)
                    (os : ('o located) IdMap.t) : unit = 
  let deps = IdMap.mapi (fun id _ -> get_dependencies (get_refs os) id) os in
  let circ =
        IdMap.filter (fun id rs -> IdSet.exists (fun r -> r = id) rs) deps in
  if IdMap.is_empty circ then ()
  else let id = fst (IdMap.choose circ) in
       let lid = loc (IdMap.find id os) in
       type_error lid (id ^ " contains a circular reference")

(* Convert a list from dl_parse_tree to IdMap *)

let check_unique_id (al : 'a list) (get_id : 'a -> id) : 'a IdMap.t = 
  let id_map = IdMap.empty in
  List.fold_left 
  (fun id_map a -> 
     let id_l = get_id a in 
     if exists_id id_map (unloc id_l) then 
       type_error (loc id_l)  ("duplicate identifier : " ^ unloc id_l)
     else IdMap.add (unloc id_l) a id_map)
  id_map al

(* EC type checks *)

let check_params (n_tl : type_binding list) : typ_tyd IdMap.t = 
  let nt_map = check_unique_id n_tl (fun nt -> nt.id) in
  IdMap.map
  (fun (nt : type_binding) -> 
     mk_loc (loc nt.id) ((check_type nt.ty), (index_of_ex nt n_tl)))
  nt_map

(* interface checks *)

let check_exists_io (ermsgpref : string) (e_io : string -> bool)
                    (io_i : comp_item) : comp_item_tyd = 
  let uid = unloc io_i.inter_id in
  if e_io uid
  then mk_loc (loc io_i.sub_id) io_i.inter_id
  else type_error
       (loc io_i.inter_id)
       (ermsgpref ^ " " ^ uid ^ " hasn't been defined yet")

let check_comp_io_body (ermsgpref : string) (e_io : string -> bool)
                       (iob : comp_item list) : inter_body_tyd = 
  let comp_item_map = check_unique_id iob (fun io_i -> io_i.sub_id) in
  Composite (IdMap.map (check_exists_io ermsgpref e_io) comp_item_map)

let check_basic_io_body (biob : message_def list) : inter_body_tyd = 
  let msg_map = check_unique_id biob (fun md -> md.id) in
  Basic
  (IdMap.map
   (fun (md : message_def) ->
      mk_loc
      (loc md.id)
      {direction = md.dir; content = (check_params md.params);
       port_label = md.port})
  msg_map)

let check_composites_ref_basics (ios : inter_tyd IdMap.t) = 
  let (composites, basics) = 
    IdMap.partition
    (fun _ ioc ->
       match (unloc ioc) with
       | Composite _ -> true
       | _           -> false)
    ios in
  let eb_io = exists_id basics in
  IdMap.iter
  (fun _ ioc -> 
     match (unloc ioc) with
     | Composite its ->
         IdMap.iter
         (fun _ idl -> 
            let uid = unloc (unloc idl) in
            if (eb_io uid) then ()
            else type_error (loc (unloc idl))
                 (uid ^ " is not a basic interface"))
         its
     | _ -> ())
  composites

let check_diradv_ios (errmsgpref : string) (da_io_map : named_inter IdMap.t) = 
  let e_io = exists_id da_io_map in
  let check_adio_def (io : named_inter) : inter_tyd = 
    match io.inter with
    | Basic iob     -> mk_loc (loc io.id) (check_basic_io_body iob)
    | Composite iob ->
        mk_loc (loc io.id) (check_comp_io_body errmsgpref e_io iob) in
  let da_ios = IdMap.map check_adio_def da_io_map in
  (check_composites_ref_basics da_ios; da_ios)

let check_dir_ios (dir_io_map : named_inter IdMap.t) =
  check_diradv_ios "direct_io" dir_io_map

let check_adv_ios (adv_io_map : named_inter IdMap.t) =
  check_diradv_ios "adversarial_io" adv_io_map
                
(* Real Functionality checks *)

let check_is_composite (ios : inter_tyd IdMap.t) (id : id) : unit = 
  let uid = unloc id in
  match unloc (IdMap.find uid ios) with
  | Basic _ ->
      type_error (loc id)
      ("the interface must be composite (even if it has only one component)")
  | Composite _ -> ()

let check_real_fun_params (dir_ios : inter_tyd IdMap.t)
                          (params : fun_param list) :
      (comp_item_tyd * int) IdMap.t = 
  let check_real_fun_param (dir_ios : inter_tyd IdMap.t) (param : fun_param) :
        (comp_item_tyd * int) = 
    let dir_i_oid = unloc param.id_dir in
    if not (exists_id dir_ios dir_i_oid)
    then type_error (loc param.id_dir)
                    ("direct_io " ^ dir_i_oid ^ " doesn't exist")
    else (check_is_composite dir_ios param.id_dir;
          (mk_loc (loc param.id) param.id_dir, index_of_ex param params)) in
  let param_map = check_unique_id params (fun p -> p.id) in
  IdMap.map (check_real_fun_param dir_ios) param_map

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

let check_state_decl (init_id : id) (s : state) : state_tyd = 
  let is_initial = (init_id = s.id) in
  let params = check_params s.params in
  let vars =
        IdMap.map
        (fun tip ->
           mk_loc (loc tip) (fst (unloc tip)))
        (check_params s.code.vars) in
  let dup = IdMap.find_first_opt (fun id -> IdMap.mem id vars) params in
  match dup with
  | None        ->
      mk_loc (loc s.id)
      {is_initial = is_initial; params = params; vars = vars;
       mmclauses = s.code.mmclauses}
  | Some (id,t) ->
      type_error (loc t)
      ("variable name " ^ id ^ " is the same as one of the states parameters")
                        
let drop_state_ctor (sd : state_def) : state = 
  match sd with 
  | InitialState s   -> s
  | FollowingState s -> s

let check_states (id : id) (code : state_def list) : state_tyd IdMap.t = 
  let init_id = check_exactly_one_initial_state id code in
  let states = List.map (fun sd -> drop_state_ctor sd) code in
  let code_map = check_unique_id states (fun s -> s.id) in
  IdMap.map (check_state_decl init_id) code_map 

type b_inter_id_path = (string list) * basic_inter_body_tyd

type r_fb_inter_id_paths =
  {direct : b_inter_id_path list; adversarial : b_inter_id_path list;
   internal : b_inter_id_path list}

let getb_inter_id_paths (root : string) (ioid : string)
                        (ios : inter_tyd IdMap.t) :
                  b_inter_id_path list = 
  let getb_body (id : string) : basic_inter_body_tyd = 
    let io = IdMap.find id ios in
    match (unloc io) with
    | Basic b -> b
    | _       ->
        failure
        ("Cannot happen, this function is called only on Basic " ^
         "interfaces") in
  let io = IdMap.find ioid ios in
  match (unloc io) with
  | Basic b       -> [([root],b)]
  | Composite cio ->
      IdMap.fold
      (fun id it l ->
         ([root; id], getb_body (unloc (unloc it))) :: l)
      cio []

let get_inter_id_paths (ioid : string) (ios : inter_tyd IdMap.t) :
                         string list list = 
  let bps = getb_inter_id_paths ioid ioid ios in
  List.map (fun bp -> fst bp) bps

let get_fun_inter_id_paths (id_dir_io : string) (id_adv_io : string option)
                           (dir_ios : inter_tyd IdMap.t)
                           (adv_ios : inter_tyd IdMap.t) :
      string list list = 
  let dir = get_inter_id_paths id_dir_io dir_ios in
  let adv =
        match id_adv_io with
        | Some id -> get_inter_id_paths id adv_ios
        | None    -> [] in
  dir @ adv

let check_i_opath (id_dir_io : string) (id_adv_io : string option)
                  (dir_ios : inter_tyd IdMap.t) (adv_ios : inter_tyd IdMap.t)
                  (iop : id list) : string list located = 
  let uiop = unlocs iop in
  let loc = mergelocs iop in
  let ps = get_fun_inter_id_paths id_dir_io id_adv_io dir_ios adv_ios in
  if (List.mem uiop ps) then mk_loc loc uiop
  else let psf = List.filter (fun p -> (List.tl p) = uiop) ps in
       match (List.length psf) with
       | 0 ->
           type_error loc
           (string_of_i_opath uiop ^
            " is not a part of the interfaces implemented by functionality")
       | 1 -> mk_loc loc (List.hd psf)
       | _ ->
           type_error loc
           (string_of_i_opath uiop ^
            " is ambiguous, it is in both direct and adversarial interfaces " ^
            "implemented by functionality")

let check_served_paths (serves : string list located list)
                       (id_dir_io : string) (pid : id) : unit = 
  let er =
        ("A party can serve at most one basic direct interface and one " ^
         "basic adversarial interface.") in
  let erone = "A party must serve one basic direct interface." in
  match (List.length serves) with
  | 0 -> type_error (loc pid)  erone
  | 1 ->
      if (List.hd (unloc (List.nth serves 0))) = id_dir_io then ()
      else type_error (loc (List.nth serves 0)) erone
  | 2 ->
      if List.hd (unloc (List.nth serves 0)) <>
         List.hd (unloc (List.nth serves 1)) then ()
      else type_error (loc (List.nth serves 1)) er
  | _ -> type_error (mergelocs serves) er
                
let check_ios_unique (iops : string list located list) : unit = 
  ignore
  (List.fold_left
   (fun l iop -> 
      let uiop = unloc iop in
      if List.mem uiop l
      then type_error (loc iop) ("parties must serve distinct interfaces")
      else uiop :: l)
   [] iops)

let check_ios_cover (id_dir_io : string) (id_adv_io : string option)
                     (dir_ios : inter_tyd IdMap.t) (adv_ios : inter_tyd IdMap.t)
                     (served_ps : string list located list) : unit = 
  let serps = unlocs served_ps in
  let ps = get_fun_inter_id_paths id_dir_io id_adv_io dir_ios adv_ios in
  let unserved = List.filter (fun p -> not (List.mem p serps)) ps in
  if (List.length unserved) = 0 then ()
  else type_error
       (mergelocs served_ps)
       ("these interfaces are not served by any party : " ^
        (string_of_i_opaths unserved))

let check_party_decl (id_dir_io : string) (id_adv_io : string option)
                     (dir_ios : inter_tyd IdMap.t) (adv_ios : inter_tyd IdMap.t)
                     (p : party_def) : party_def_tyd = 
  let serves =
        List.map
        (check_i_opath id_dir_io id_adv_io dir_ios adv_ios)
        p.serves in
  let () = check_served_paths serves id_dir_io p.id in
  let code = check_states p.id p.states in
  mk_loc (loc p.id) {serves = serves; states = code}

let check_parties_serve_direct_sum (parties : party_def_tyd IdMap.t)
      (id_dir_io : string) (id_adv_io : string option)
      (dir_ios : inter_tyd IdMap.t) (adv_ios : inter_tyd IdMap.t) : unit = 
  let served_ps =
        IdMap.fold (fun _ p l -> l @ (unloc p).serves) parties [] in
  let () = check_ios_unique served_ps in
  check_ios_cover id_dir_io id_adv_io dir_ios adv_ios served_ps

let get_real_fun_sub_item_id (si : sub_item) : id = 
  match si with
  | SubFunDecl sf -> sf.id
  | PartyDef p    -> p.id

let check_exists_dir_io (dir_ios : inter_tyd IdMap.t) (id_dir_io : id) = 
  let uid_dir_io = unloc id_dir_io in
  if exists_id dir_ios uid_dir_io then () 
  else type_error (loc id_dir_io)
       ("direct_io " ^ uid_dir_io ^ " doesn't exist")

let check_exists_i2_sio (i2s_ios : inter_tyd IdMap.t) (id_i2_sio : id) = 
  let uid_i2_sio = unloc id_i2_sio in
  if exists_id i2s_ios uid_i2_sio
  then match unloc (IdMap.find uid_i2_sio i2s_ios) with
       | Basic _     -> ()
       | Composite _ ->
           type_error (loc id_i2_sio)
           "this adversarial interface cannot be composite"
        else type_error (loc id_i2_sio)
             ("adversarial interface " ^ uid_i2_sio ^ " doesn't exist")

let check_fun_decl
    (e_f_id : string -> bool) (is_real_fun_id : string -> bool)
    (dir_ios : inter_tyd IdMap.t) (adv_ios : inter_tyd IdMap.t)
    (r_fun : fun_def) : fun_tyd =
  let params = check_real_fun_params dir_ios r_fun.params in 
  let () = check_exists_dir_io dir_ios r_fun.id_dir in
  let id_dir_io = unloc r_fun.id_dir in 
  let id_adv_io =
        match r_fun.id_adv with
        | None    -> None
        | Some id -> 
            (let uid = unloc id in
             if exists_id adv_ios uid then Some uid
             else type_error (loc id)
                  ("adversarial interface " ^ uid ^ " doesn't exist")) in
  match r_fun.fun_body with
  | FunBodyReal sub_items  ->
      let sub_items = check_unique_id sub_items get_real_fun_sub_item_id in
      let () =
        let dup_ids =
          IdMap.filter (fun id _ -> IdMap.mem id params) sub_items in
        if IdMap.is_empty dup_ids then ()
        else let id, dup = IdMap.choose dup_ids in
             let lc = loc (get_real_fun_sub_item_id dup) in
             type_error lc
             ("the name " ^ id ^
              " is the same name as one of the functionality's parameters") in
      let sf_map =
        filter_map
        (fun sub_i ->
           match sub_i with
           | SubFunDecl sf -> Some sf
           | _             -> None)
        sub_items in
      let check_sub_fun_decl (e_f_id : string -> bool) (sf : sub_fun_decl)
                               : sub_fun_decl_tyd =
        let fun_id = unloc sf.fun_id in
        if not (e_f_id fun_id)
          then type_error (loc sf.fun_id)
               ("nonexisting functionality : " ^ fun_id)
        else if is_real_fun_id fun_id
          then type_error (loc sf.fun_id)
               (fun_id ^ " is not an ideal functionality")
        else mk_loc (loc sf.id) {fun_id = fun_id} in
      let sub_funs =
        IdMap.map (check_sub_fun_decl e_f_id) sf_map in
      let () = check_is_composite dir_ios r_fun.id_dir in
      let parties =
        let () =
          match r_fun.id_adv with
          | Some id -> check_is_composite adv_ios id
          | _       -> () in
        let p_map =
          filter_map
          (fun sub_i ->
             match sub_i with
             | PartyDef p -> Some p
             | _          -> None)
          sub_items in
        let ps =
          IdMap.map
          (check_party_decl id_dir_io id_adv_io dir_ios adv_ios)
          p_map in
        (check_parties_serve_direct_sum ps id_dir_io id_adv_io
         dir_ios adv_ios;
         ps) in
      mk_loc (loc r_fun.id)
      (FunBodyReal
       {params = params; id_dir_io = id_dir_io; id_adv_io = id_adv_io;
        sub_funs = sub_funs; parties = parties})
  | FunBodyIdeal state_defs ->
      let () = check_is_composite dir_ios r_fun.id_dir in
      let states =
        match r_fun.id_adv with
        | None ->
            type_error (loc r_fun.id)
            ("an ideal functionality must implement a basic adversarial " ^
             "interface")
        | Some id ->
            (check_exists_i2_sio adv_ios id;
             check_states r_fun.id state_defs) in
      mk_loc (loc r_fun.id)
      (FunBodyIdeal
       {id_dir_io = id_dir_io; id_adv_io = Option.get id_adv_io;
        states = states})

let get_dir_io_id_impl_by_fun (fid : string) (funs : fun_tyd IdMap.t) :
                                string = 
  let func = IdMap.find fid funs in
  match unloc func with
  | FunBodyReal fbr -> fbr.id_dir_io
  | FunBodyIdeal fbi -> fbi.id_dir_io

let get_param_dir_io_ids (r_funs : fun_tyd IdMap.t) (rfid : string) :
                           string list = 
  let func = IdMap.find rfid r_funs in
  match unloc func with
  | FunBodyReal fbr -> unlocs (unlocs (to_list fbr.params))
  | FunBodyIdeal _  -> []

type state_vars =
  {flags : string list; internal_ports : QidSet.t; consts : typ IdMap.t;
   vars : typ IdMap.t; initialized_vs : IdSet.t}

let init_state_vars (s : state_body) (ports : QidSet.t)
                    (flags : string list) : state_vars = 
  let consts = IdMap.map (fun p -> fst (unloc p)) s.params in
  let vars = IdMap.map (fun v -> unloc v) s.vars in
  {flags = flags; internal_ports = ports; consts = consts;
   vars = vars; initialized_vs = IdSet.empty}

type state_sig = typ list

let get_state_sig (s : state_body) : state_sig = 
  if s.is_initial then []
  else let ps = IdMap.bindings s.params in
       let ts = unlocs (snd (List.split ps)) in
       let tord = List.sort (fun t1 t2 -> snd t1 - snd t2) ts in
       (fst (List.split tord))

let get_state_sigs (states : state_tyd IdMap.t) : state_sig IdMap.t = 
  IdMap.map (fun s -> get_state_sig (unloc s) ) states

let string_of_msg_path (mp : msg_path) : string = 
  let siop = string_of_i_opath (unlocs mp.inter_id_path) in
  match mp.msg_or_other with 
  | MsgPathId id -> siop ^ "." ^ (unloc id)
  | MsgPathOtherMsg _ -> siop ^ ".othermsg"

let string_of_msg_pathl (mpl : msg_path list) : string = 
  string_of_stringl (List.map (fun mp -> string_of_msg_path mp) mpl)

let filterb_io_ps (dir : msg_dir) (biops : b_inter_id_path list) :
                    b_inter_id_path list = 
  List.map
  (fun biop ->
         (fst biop,
          IdMap.filter
          (fun _ md -> (unloc md).direction = dir)
          (snd biop)))
  biops

let get_incoming_msg_paths (bps : r_fb_inter_id_paths) : r_fb_inter_id_paths = 
  { direct = filterb_io_ps In bps.direct;
    adversarial = filterb_io_ps In bps.adversarial;
    internal = filterb_io_ps Out bps.internal }

let get_outgoing_msg_paths (bps : r_fb_inter_id_paths) : r_fb_inter_id_paths = 
  { direct = filterb_io_ps Out bps.direct;
    adversarial = filterb_io_ps Out bps.adversarial;
    internal = filterb_io_ps In bps.internal }

let msg_loc (mp : msg_path) : EcLocation.t = 
  match mp.msg_or_other with
  | MsgPathId id -> loc id
  | MsgPathOtherMsg l -> l

let msg_paths_of_b_inter_id_path (bp : b_inter_id_path) : msg_path list =   
  IdMap.fold
  (fun id _ l ->
         { inter_id_path = dummylocl (fst bp);
           msg_or_other = MsgPathId (dummyloc id) } :: l)
  (snd bp) []

let mp_of_bpl (bpl : b_inter_id_path list) : msg_path list = 
  List.flatten (List.map (fun bp -> msg_paths_of_b_inter_id_path bp) bpl)

let flatten_r_fb_inter_id_paths (bps : r_fb_inter_id_paths) : b_inter_id_path list = 
  bps.direct @ bps.adversarial @ bps.internal

let msg_paths_of_r_fb_inter_id_paths (bps : r_fb_inter_id_paths) : msg_path list = 
  mp_of_bpl (flatten_r_fb_inter_id_paths bps)

let check_msg_path (bps : r_fb_inter_id_paths) (mp : msg_path) : msg_path = 
  let ips = mp_of_bpl bps.internal in
  let allps = msg_paths_of_r_fb_inter_id_paths bps in       
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
               ("the message is unexpected. these messages are expected : " ^
                string_of_msg_pathl allps) in
  let ambiguous (mtch : msg_path list) = 
    type_error (msg_loc mp)
               ("the message is ambiguous. there are multiple messages " ^
                "that match the description : " ^ string_of_msg_pathl mtch) in
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

let msg_paths_of_r_fb_inter_id_paths_w_othermsg (bps : r_fb_inter_id_paths) :
                                            msg_path list = 
  let mps = msg_paths_of_r_fb_inter_id_paths bps in
  let omps =
        List.map
        (fun bp ->
             { inter_id_path = dummylocl (fst bp);
               msg_or_other = MsgPathOtherMsg _dummy })
        (flatten_r_fb_inter_id_paths bps) in
  mps @ omps

let check_mm_ds_non_empty (bps : r_fb_inter_id_paths) (mpl : msg_path list) :
                            msg_path list = 
  let mps = msg_paths_of_r_fb_inter_id_paths_w_othermsg bps in
  List.fold_left (fun mps mp -> remove_covered_paths mps mp) mps mpl

let check_msg_match_deltas (rfbps : r_fb_inter_id_paths) (mml : msg_pat list) :
                             unit = 
  let mps = get_incoming_msg_paths rfbps in
  let r =
        check_mm_ds_non_empty
        mps (List.map (fun (mm : msg_pat) -> mm.path) mml) in
  if r<>[]
  then let l = msg_loc ((List.hd (List.rev mml)).path)
       in type_error l
          ("message match is not exhaustive, these " ^
           "messages are not matched : " ^ string_of_msg_pathl r)
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
  then type_error (loc cid) (ucid ^ " is already used")
  else {flags = sv.flags; internal_ports = sv.internal_ports;
        consts = IdMap.add ucid ct sv.consts; vars = sv.vars;
        initialized_vs = sv.initialized_vs}

let check_port_var_binding (bps : r_fb_inter_id_paths) (mp : string list)
                           (vid : id) (sv : state_vars) : state_vars = 
  let d = List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.direct in
  let i =
    List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.internal in
  let a =
    List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.adversarial in
  if not (d && not i && not a)
  then type_error (loc vid)
       ("the message " ^ string_of_i_opath mp ^
        " maybe isn't an incoming message of a direct_io served by the " ^
        "party and cannot bind the source port to a variable")
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
    (ps : b_inter_id_path list) (mp : string list*string)
    (tm : pat list) (sv : state_vars) : state_vars = 
  let p = List.find (fun p -> (fst p) = (fst mp)) ps in
  let mt = to_list (unlocm((unloc(IdMap.find (snd mp) (snd p))).content)) in
  if List.length mt <> List.length tm
  then type_error (get_loc_match_item_list tm)
       ("the number of bindings is different then the number " ^
        "of message parameters")
  else List.fold_left2 check_item_type_add_binding sv tm mt

let check_pat_args (bps : b_inter_id_path list) (mm : msg_pat)
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
          check_msg_content_bindings bps
          ((unlocs mm.path.inter_id_path),(unloc id)) mil sv

let check_match_bindings (bps : r_fb_inter_id_paths) (mm : msg_pat)
                         (sv : state_vars) : state_vars = 
  let sv' =        
    match mm.port_id with
    | Some id -> check_port_var_binding bps (unlocs mm.path.inter_id_path) id sv
    | None    -> sv in
  let ps = bps.direct@bps.adversarial@bps.internal in
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
        type_error (loc si.id) ("non-existing state : " ^ (unloc si.id)) in
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

let check_msg_content_values (es : expression_l list) (mc : typ_tyd IdMap.t)
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

let check_send_direct (msg : msg_expr) (mc : typ_tyd IdMap.t)
                      (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_id with
    | Some p ->
        (check_exists_and_has_compatible_type p port_type sv;
         check_initialized sv p)
    | None   -> type_error l ("missing destination port") in
  check_msg_content_values msg.args mc sv

let check_send_adversarial (msg : msg_expr) (mc : typ_tyd IdMap.t)
                           (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_id with
    | Some _ ->
        type_error l "only direct messages can have destination port"
    | None   -> () in
  check_msg_content_values msg.args mc sv

let check_send_internal (msg : msg_expr) (mc : typ_tyd IdMap.t)
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

let is_msg_path_inb_inter_id_paths (mp : msg_path) (bps : b_inter_id_path list) : bool = 
  let bpo = List.find_opt (fun bp -> fst bp = unlocs mp.inter_id_path) bps in
  match bpo with
  | Some _ -> true
  | None   -> false

let get_msg_def_for_msg_path (mp : msg_path) (bs : b_inter_id_path list) :
                               message_def_body = 
  let iop = unlocs mp.inter_id_path in
  let bio = List.find (fun bp -> (fst bp) = iop) bs in
  let mt  =
    match mp.msg_or_other with
    | MsgPathId id -> unloc id
    | MsgPathOtherMsg _ ->
        failure "MsgPathOtherMsg doesn't have definition in interface" in
  let mdb = IdMap.find mt (snd bio) in
  unloc mdb

let check_send_msg_path (msg : msg_expr) (bps : r_fb_inter_id_paths)
                        (sv : state_vars) : msg_expr = 
  let ps = get_outgoing_msg_paths bps in
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

let check_send (msg : msg_expr) (bps : r_fb_inter_id_paths)
               (sv : state_vars) : msg_expr = 
  let msg' = check_send_msg_path msg bps sv in
  let bs = bps.direct@bps.adversarial@bps.internal in
  let mdbc = (get_msg_def_for_msg_path msg'.path bs).content in
  let () =
    match msg'.path with
    | ( _ as p) when is_msg_path_inb_inter_id_paths p bps.direct ->
        check_send_direct msg' mdbc sv
    | ( _ as p) when is_msg_path_inb_inter_id_paths p bps.adversarial ->
        check_send_adversarial msg' mdbc sv
    | ( _ as p) when is_msg_path_inb_inter_id_paths p bps.internal ->
        check_send_internal msg' mdbc sv
    | _ ->
        failure
        ("impossible - the path is always in one of direct|" ^
         "adversarial|internal") in
  msg'

let check_send_and_transition (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                              (sat : send_and_transition) (sv : state_vars) :
                                instruction = 
  let msg' = check_send sat.msg_expr bps sv in
  let () = check_transition sat.state_expr ss sv in
  SendAndTransition {msg_expr = msg'; state_expr = sat.state_expr}

let merge_state_vars (sv1 : state_vars) (sv2 : state_vars) : state_vars = 
  {flags = sv1.flags; internal_ports = sv1.internal_ports;
   consts = sv1.consts; vars = sv1.vars;
   initialized_vs = IdSet.inter sv1.initialized_vs sv2.initialized_vs}

let rec check_ite (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                  (sv : state_vars) (ex : expression_l)
                  (tins : instruction_l list)
                  (eins : instruction_l list option) :
                    instruction*state_vars = 
  if check_expression sv ex <> bool_type
  then type_error (loc ex) "the condition must be a boolean expression"
  else let (tins_c, eins_c, sv') = check_branches bps ss sv tins eins in
       (ITE (ex, tins_c, eins_c), sv')

and check_branches (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                   (sv : state_vars) (tins : instruction_l list)
                   (eins : instruction_l list option) :
                     instruction_l list * instruction_l list option *
                     state_vars = 
  let (tins_c,tsv) = check_instructions bps ss sv tins in
  let (eins_c,esv) =
    match eins with                         
    | Some is ->
        let (is',esv) = check_instructions bps ss sv is in (Some is',esv)
    | None    -> (None, sv) in
  let sv' = merge_state_vars tsv esv in
  (tins_c, eins_c, sv')

and check_decode (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
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
              check_branches bps ss sv' okins (Some erins) in
            ((Decode (ex, ty, m_is, okins_c, Option.get erins_c)), sv'')

and check_instruction (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                      (insv : instruction_l list*state_vars)
                      (i : instruction_l) : instruction_l list * state_vars = 
  let ins = fst insv in
  let sv = snd insv in
  match unloc i with
  | Assign (vid, ex)      -> (ins @ [i], check_val_assign sv vid ex)
  | Sample (vid, ex)      -> (ins @ [i], check_sampl_assign sv vid ex)
  | ITE (ex, tins, eins)  ->
      let (ite_c, sv') = check_ite bps ss sv ex tins eins in
      (ins @ [mk_loc (loc i) ite_c], sv')
  | Decode (ex, ty, m_is, okins, erins) ->
      let (match_c,sv') = check_decode bps ss sv ex ty m_is okins erins in
      (ins @ [mk_loc (loc i) match_c], sv')
  | SendAndTransition sat ->
      (ins @ [mk_loc (loc i) (check_send_and_transition bps ss sat sv)]), sv
  | Fail                  -> (ins @ [i], sv)

and check_instructions (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                       (sv : state_vars) (is : instruction_l list) :
                         (instruction_l list * state_vars) = 
  List.fold_left (check_instruction bps ss) ([],sv) is

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

let check_msg_code (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                   (sv : state_vars) (is : instruction_l list) :
                     instruction_l list = 
  let is_tyd = fst (check_instructions bps ss sv is) in
  let () = check_ends_are_sa_tor_f is_tyd in
  is_tyd

let check_message_path (bps : r_fb_inter_id_paths) (mmc : msg_match_clause) :
                         msg_match_clause = 
  let path' =
    check_msg_path (get_incoming_msg_paths bps) mmc.msg_pat.path in
  {msg_pat =
     {port_id = mmc.msg_pat.port_id;
      path = path'; pat_args = mmc.msg_pat.pat_args};
   code = mmc.code}

let check_m_mcode (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                  (sv : state_vars) (mmc : msg_match_clause) : msg_match_clause = 
  let mmc' = check_message_path bps mmc in 
  let sv' = check_match_bindings bps mmc'.msg_pat sv in
  let code' = check_msg_code bps ss sv' mmc'.code in
  {msg_pat = mmc'.msg_pat; code = code'}

let check_state_code (bps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                     (sv : state_vars) (mmclauses : msg_match_clause list) :
                       msg_match_clause list = 
  let mmclauses' = List.map (fun mmc -> check_m_mcode bps ss sv mmc) mmclauses in
  let () =
    check_msg_match_deltas bps
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

let filterb_inter_id_paths (bps : b_inter_id_path list) (pfxs : string list located list) :
                       b_inter_id_path list = 
  List.filter
  (fun bp -> List.exists (fun pfx -> unloc pfx = fst bp) pfxs)
  bps

let get_fb_inter_id_paths (dir_ios : inter_tyd IdMap.t)
                          (adv_ios : inter_tyd IdMap.t)
                          (f : fun_tyd) : r_fb_inter_id_paths = 
  let uf = unloc f in
  let iddir = id_dir_io_of_fun_body_tyd uf in
  let direct = getb_inter_id_paths iddir iddir dir_ios in
  let adversarial = 
    match id_adv_io_of_fun_body_tyd uf with
    | Some id -> getb_inter_id_paths id id adv_ios
    | None -> [] in
  {direct = direct; adversarial = adversarial; internal = []}

let get_r_fb_inter_id_paths (dir_ios : inter_tyd IdMap.t)
                      (adv_ios : inter_tyd IdMap.t)
                      (funs : fun_tyd IdMap.t) (r_f : fun_tyd)
                      (p : party_def_tyd) : r_fb_inter_id_paths = 
  let all = get_fb_inter_id_paths dir_ios adv_ios r_f in
  let ur_f = unloc r_f in
  let filt = (unloc p).serves in
  let direct =  filterb_inter_id_paths all.direct filt in
  let adversarial = filterb_inter_id_paths all.adversarial filt in
  let internal_sfm =
    IdMap.mapi
    (fun sfid (sf : sub_fun_decl_tyd) ->
           let did = get_dir_io_id_impl_by_fun ((unloc sf).fun_id) funs in
           getb_inter_id_paths sfid did dir_ios)
    (sub_funs_of_fun_body_tyd ur_f) in
  let internal_pm =
    IdMap.mapi
    (fun pid p -> 
           let did = unloc (unloc (fst p)) in
           getb_inter_id_paths pid did dir_ios)
    (params_of_fun_body_tyd ur_f) in
  let internal_m =
    IdMap.union
    (fun _ _ _ ->
       failure
       ("Impossible, we already checked params and " ^
        "subfuns have different ids"))
    internal_sfm internal_pm in
  let internal = IdMap.fold (fun _ bps l -> l @ bps) internal_m [] in
  {direct = direct; adversarial = adversarial; internal = internal}

let check_state (ur_f : fun_body_tyd) (states : state_tyd IdMap.t)
                (bps : r_fb_inter_id_paths) (s : state_tyd) : state_tyd = 
  let us = unloc s in
  let sv = init_state_vars (unloc s) (get_internal_ports ur_f) [] in
  let ss = get_state_sigs states in
  let mmclauses' = check_state_code bps ss sv us.mmclauses in
  mk_loc (loc s)
         {is_initial = us.is_initial; params = us.params; vars = us.vars;
          mmclauses = mmclauses'}

let check_party_code dir_ios adv_ios funs = 
  IdMap.map 
  (fun r_f -> 
     match unloc r_f with
     | FunBodyReal ur_f ->
         let parties = ur_f.parties in
         let parties' =
           IdMap.map 
           (fun p -> 
              let up = unloc p in
              let bps = get_r_fb_inter_id_paths dir_ios adv_ios funs r_f p in
              let states = up.states in
              let states' =
                IdMap.map (check_state (unloc r_f) states bps) states  in
              mk_loc (loc p) {serves = up.serves; states = states'})
           parties in
         mk_loc (loc r_f)
         (FunBodyReal
          {params = ur_f.params; id_dir_io = ur_f.id_dir_io;
           id_adv_io = ur_f.id_adv_io; sub_funs = ur_f.sub_funs;
           parties = parties'})
     | FunBodyIdeal ur_f ->
         let states = ur_f.states in
         let bps = get_fb_inter_id_paths dir_ios adv_ios r_f in
         let states' = IdMap.map (check_state (unloc r_f) states bps) states in
         mk_loc (loc r_f)
         (FunBodyIdeal
          {id_dir_io = ur_f.id_dir_io; id_adv_io = ur_f.id_adv_io;
           states = states'}))
  funs

let get_sf_refs_to_f_in_rf (funs : fun_tyd IdMap.t) (fid : string) : IdSet.t = 
  match unloc (IdMap.find fid funs) with
  | FunBodyReal fbr ->
      let sfrf =
        IdMap.filter
        (fun _ r -> exists_id funs (unloc r).fun_id)
        fbr.sub_funs in
  IdMap.fold (fun _ r set -> IdSet.add (unloc r).fun_id set) sfrf IdSet.empty
  | FunBodyIdeal _  -> IdSet.empty

let check_circ_refs_in_r_funs (rfs : fun_tyd IdMap.t) =
  check_circ_refs get_sf_refs_to_f_in_rf rfs

let check_funs (fun_map : fun_def IdMap.t) (dir_ios : inter_tyd IdMap.t)
               (adv_ios : inter_tyd IdMap.t) : fun_tyd IdMap.t = 
  let e_f_id = exists_id fun_map in 
  let is_real_fun_id id =
    try let fun_def = IdMap.find id fun_map in
        is_real_fun_body (fun_def.fun_body) with
      Not_found -> false in
  let funs =
    IdMap.map
    (check_fun_decl e_f_id is_real_fun_id dir_ios adv_ios)
    fun_map in
  (check_circ_refs_in_r_funs funs;
   check_party_code dir_ios adv_ios funs)

(* Simulator checks *)

let check_msg_code_sim (fbps : r_fb_inter_id_paths) (ss : state_sig IdMap.t)
                       (mmc : msg_match_clause) (sv : state_vars) :
                         msg_match_clause = 
  let code' = check_msg_code fbps ss sv mmc.code in
  {msg_pat = mmc.msg_pat; code = code'}

let check_message_path_sim (bps : b_inter_id_path list) (isini : bool)
                           (mmc : msg_match_clause) : unit = 
  let bps = filterb_io_ps In bps in
  let mp = mmc.msg_pat.path in
  let l = msg_loc mp in
  let id = fst (List.find (fun p -> (List.length (fst p)) = 1) bps) in
  if isini && unlocs mp.inter_id_path <> id
  then type_error l
       ("initial state can handle only messages comming " ^
        "from ideal functionality. did you omit prefix " ^
        List.hd id ^ ".?")
  else let iops = fst(List.split bps) in
       let invalid_dest() =
         type_error l
         ("not a valid destination, these destinations are " ^
          "valid : " ^ string_of_i_opaths iops) in
       let umpiop = (unlocs mp.inter_id_path) in
       match mp.msg_or_other with
       | MsgPathId mt ->
           if not(List.mem umpiop iops)
             then invalid_dest()
           else if List.exists
                   (fun bp ->
                          fst bp = umpiop &&
                          IdMap.mem (unloc mt) (snd bp))
                   bps
             then ()
           else type_error (loc mt)
                (unloc mt ^ " is not an incoming message of " ^
                 string_of_i_opath umpiop)
       | MsgPathOtherMsg _ ->
           if List.exists
              (fun p -> sl1_starts_with_sl2 p umpiop)
              iops
           then ()
           else invalid_dest ()

let check_match_bindings_sim (bps : b_inter_id_path list) (sv : state_vars)
                             (mmc : msg_match_clause) : state_vars = 
  let mm = mmc.msg_pat in
  check_pat_args bps mm sv

let check_msg_match_deltas_sim (rfbps : r_fb_inter_id_paths)
                               (mmclauses : msg_match_clause list) : unit = 
  let mps = get_incoming_msg_paths rfbps in
  ignore
  (check_mm_ds_non_empty mps
   (List.map
    (fun mmc ->
          {inter_id_path = mmc.msg_pat.path.inter_id_path;
           msg_or_other = mmc.msg_pat.path.msg_or_other})
    mmclauses))

let check_sim_state_code (bps : b_inter_id_path list) (ss : state_sig IdMap.t)
                         (sv : state_vars) (isini : bool)
                         (mmclauses : msg_match_clause list) :
                           msg_match_clause list = 
  let () = List.iter (check_message_path_sim bps isini) mmclauses in
  let svs = List.map (check_match_bindings_sim bps sv) mmclauses in
  let fbps = {direct = []; adversarial = bps; internal = []} in
  let ret = List.map2 (check_msg_code_sim fbps ss) mmclauses svs in
  let () = check_msg_match_deltas_sim fbps ret in
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
                 (get_sc funs (unloc sfd).fun_id (pfx @ [sfid])) :: l)
          (sub_funs_of_fun_body_tyd urf) [])
    else failure
         ("Impossible! We already checked that all referenced " ^
          "functionalities exist") in
  let urf = unloc(IdMap.find r_f funs) in
  let pids =
    IdMap.fold (fun pid _ l -> pid :: l) (params_of_fun_body_tyd urf) [] in
  let qpids = List.map (fun pid -> r_f :: [pid]) pids in
  disj_union(get_sc funs r_f [r_f] :: List.map2 (get_sc funs) ps qpids)
                
let get_component_inter_id_paths (adv_ios : inter_tyd IdMap.t)
                                 (f : fun_body_tyd) : b_inter_id_path list = 
  match id_adv_io_of_fun_body_tyd f with
  | Some id -> getb_inter_id_paths id id adv_ios 
  | None    -> []

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In

let invert_mdf (mdf : message_def_body) : message_def_body = 
  {direction = (invert_dir mdf.direction);
   content = mdf.content; port_label = mdf.port_label}

let invert_md_fl (mdfl : message_def_body located) : message_def_body located = 
  let l = loc mdfl in
  let mdf = unloc mdfl in
  let mdf' = invert_mdf mdf in
  mk_loc l mdf'

let invertb_i_ob_tyd (bio : basic_inter_body_tyd) : basic_inter_body_tyd = 
  IdMap.map invert_md_fl bio

let invert_msg_dirs (bp : b_inter_id_path) : b_inter_id_path = 
  let bio = snd bp in
  let bio' = invertb_i_ob_tyd bio in
  (fst bp, bio')

let get_simb_inter_id_paths (adv_ios : inter_tyd IdMap.t) (uses : string)
                      (cs : fun_body_tyd QidMap.t) : b_inter_id_path list = 
  let sbps = QidMap.map (get_component_inter_id_paths adv_ios) cs in        
  let bps =
    QidMap.add
    []
    (List.map
     (fun bp -> invert_msg_dirs bp)
     (getb_inter_id_paths uses uses adv_ios))
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
        
let check_sim_code (_ : inter_tyd IdMap.t) (adv_ios : inter_tyd IdMap.t)
                   (funs : fun_tyd IdMap.t) (sim : sim_def_tyd) : sim_def_tyd = 
  let usim = unloc sim in
  let states = usim.states in
  let ss = get_state_sigs states in
  let cs = get_sim_components funs usim.sims usim.sims_arg_ids in
  let bps = get_simb_inter_id_paths adv_ios usim.uses cs in
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
  else type_error (loc rf) ("functionality " ^ urf ^ " doesn't exist")

let check_is_real_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let () = check_exists_f funs rf in
  let f = unloc (IdMap.find (unloc rf) funs) in
  if not (is_real_fun_body_tyd f)
  then type_error (loc rf)
       ("the simulated functionality must be a real functionality")

let check_sim_fun_params (funs : fun_tyd IdMap.t) (_ : inter_tyd IdMap.t)
                         (rf : id) (params : id list) = 
  let d_ios = get_param_dir_io_ids funs (unloc rf) in
  let d_ios' =
    List.map
    (fun id -> get_dir_io_id_impl_by_fun id funs) (unlocs params) in
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
              | FunBodyReal _ ->
                  type_error (loc pid)
                  ("the argument to simulated functionality must " ^
                   "be an ideal functionality")
              | FunBodyIdeal _  ->
                  (* we know the ideal functionality implements a basic
                     adversarial interface *)
                  ())
       params

let check_sim_decl (_ : inter_tyd IdMap.t) (i2s_ios : inter_tyd IdMap.t)
                   (funs : fun_tyd IdMap.t) (sd : sim_def) : sim_def_tyd = 
  let () = check_exists_i2_sio i2s_ios sd.uses in
  let uses = unloc sd.uses in
  let () = check_is_real_f funs sd.sims in
  let sims = unloc sd.sims in
  let () = List.iter (check_exists_f funs) sd.sims_arg_ids in
  let () = check_sim_fun_params funs i2s_ios sd.sims sd.sims_arg_ids in
  let sims_param_ids = unlocs sd.sims_arg_ids in
  let body = check_states sd.id sd.states in
  mk_loc (loc sd.id)
  {uses = uses; sims = sims; sims_arg_ids = sims_param_ids; states = body}

let check_simulators (sim_map : sim_def IdMap.t) (dir_ios : inter_tyd IdMap.t)
                     (adv_ios : inter_tyd IdMap.t) (funs : fun_tyd IdMap.t) :
                       sim_def_tyd IdMap.t = 
  let sims = IdMap.map (check_sim_decl dir_ios adv_ios funs) sim_map in
  IdMap.map (check_sim_code dir_ios adv_ios funs) sims

(* DL prog checks *)

let get_io_id io_def = match io_def with
  | AdversarialInter io -> io.id
  | DirectInter io      -> io.id

let get_def_id (def : def) = match def with
  | InterDef iod -> get_io_id iod
  | FunDef fd -> fd.id
  | SimDef sd -> sd.id

let filter_map (fm : 'a -> 'b option) (m : 'a IdMap.t) : 'b IdMap.t = 
  let flt =
    IdMap.filter
    (fun _ def ->
           match fm def with
           | Some _ -> true
           | None -> false)
    m in
  IdMap.map
  (fun def ->
         match fm def with
         | Some x -> x
         | None   -> failure "!impossible!")
  flt

let check_defs def_l = 
  let def_map = check_unique_id def_l get_def_id in
  let dir_io_map =
    filter_map
    (fun def ->
           match def with
           | InterDef DirectInter io -> Some io
           | _ -> None)
    def_map in
  let adv_io_map =
    filter_map
    (fun def ->
           match def with
           | InterDef AdversarialInter io -> Some io
           | _ -> None)
    def_map in
  let fun_map =
    filter_map
    (fun def ->
           match def with
           | FunDef f -> Some f
           | _ -> None)
    def_map in
  let sim_map =
    filter_map
    (fun def ->
           match def with
           | SimDef sd -> Some sd
           | _ -> None)
    def_map in
  let dir_ios = check_dir_ios dir_io_map in
  let adv_ios = check_adv_ios adv_io_map in
  let funs = check_funs fun_map dir_ios adv_ios in
  let sims = check_simulators sim_map dir_ios adv_ios funs in
  { direct_ios = dir_ios; adversarial_ios = adv_ios;
    functionalities = funs; simulators = sims }

(* TODO : redundant code? *)
let load_uc_imports _ : def list = []

let load_ec_reqs reqs = 
  let reqimp idl = 
    try UcEcInterface.require_import (unloc idl) with
    Failure f ->
      type_error (loc idl)
      ("error when importing EasyCrypt theory " ^ unloc idl ^ ":\n" ^ f) in
  List.iter reqimp reqs

let typecheck spec = 
  let () = UcEcInterface.init() in
  let () = load_ec_reqs spec.externals.ec_requirements in
  let ext_defs = load_uc_imports spec.externals.dl_imports in
  check_defs (ext_defs @ spec.definitions)
