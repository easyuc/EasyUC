(* UcTypecheck module *)

(* Typecheck a specification *)

open Batteries
open EcLocation
open UcEcTypes
open UcTypes
open UcSpec
open UcTypedSpec
open UcUtils

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
       type_error lid (id^ " contains a circular reference.")

(* Convert a list from dl_parse_tree to IdMap *)

let check_unique_id (al : 'a list) (get_id : 'a -> id) : 'a IdMap.t = 
  let id_map = IdMap.empty in
  List.fold_left 
  (fun id_map a -> 
     let id_l = get_id a in 
     if exists_id id_map (unloc id_l) then 
       type_error (loc id_l)  ("Duplicate identifier : " ^ (unloc id_l))
     else IdMap.add (unloc id_l) a id_map)
  id_map al

(* EC type checks *)

let check_params (n_tl : name_type list) : typ_tyd IdMap.t = 
  let nt_map = check_unique_id n_tl (fun nt -> nt.id) in
  IdMap.map
  (fun (nt : name_type) -> 
     mk_loc (loc nt.id) ((check_type nt.ty), (index_of_ex nt n_tl)))
  nt_map

(* IO checks *)

let check_exists_io (ermsgpref : string) (e_io : string -> bool)
                    (io_i : comp_item) : comp_item_tyd = 
  let uid = unloc io_i.inter_id in
  if e_io uid
  then mk_loc (loc io_i.sub_id) io_i.inter_id
  else type_error
       (loc io_i.inter_id)
       (ermsgpref ^ " " ^ uid ^ " hasn't been defined yet.")

let check_comp_io_body (ermsgpref : string) (e_io : string -> bool)
                       (iob : comp_item list) : io_body_tyd = 
  let comp_item_map = check_unique_id iob (fun io_i -> io_i.sub_id) in
  Composite (IdMap.map (check_exists_io ermsgpref e_io) comp_item_map)

let check_basic_io_body (biob : message_def list) : io_body_tyd = 
  let msg_map = check_unique_id biob (fun md -> md.id) in
  Basic
  (IdMap.map
   (fun (md : message_def) ->
      mk_loc
      (loc md.id)
      {direction = md.dir; content = (check_params md.params);
       port_label = md.port})
  msg_map)

let check_composites_ref_basics (ios : io_tyd IdMap.t) = 
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
            else type_error (loc (unloc idl)) (uid ^ " is not a basic IO."))
         its
     | _ -> ())
  composites

let check_diradv_ios (errmsgpref : string) (da_io_map : named_inter IdMap.t) = 
  let e_io = exists_id da_io_map in
  let check_adio_def (io : named_inter) : io_tyd = 
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

let check_is_composite (ios : io_tyd IdMap.t) (id : id) : unit = 
  let uid = unloc id in
  match unloc (IdMap.find uid ios) with
  | Basic _ ->
      type_error (loc id)
      ("The IO must be composite (even if it has only one component).")
  | Composite _ -> ()

let check_real_fun_params (dir_ios : io_tyd IdMap.t)
                          (params : fun_param list) :
      (comp_item_tyd * int) IdMap.t = 
  let check_real_fun_param (dir_ios : io_tyd IdMap.t) (param : fun_param) :
        (comp_item_tyd * int) = 
    let dir_i_oid = unloc param.id_dir in
    if not (exists_id dir_ios dir_i_oid)
    then type_error (loc param.id_dir)
                    ("direct_io " ^ dir_i_oid ^ " doesn't exist.")
    else (check_is_composite dir_ios param.id_dir;
          (mk_loc (loc param.id) param.id_dir, index_of_ex param params)) in
  let param_map = check_unique_id params (fun p -> p.id) in
  IdMap.map (check_real_fun_param dir_ios) param_map

let check_sub_fun_decl (e_f_id : string -> bool) (e_param : string -> bool)
                       (e_sf_id : string -> bool) (sf : sub_fun_decl) :
                       sub_fun_decl_tyd = 
  let fun_id = unloc sf.fun_id in
  (if e_f_id fun_id
   then (List.iter
         (fun p ->
            let up = unloc p in
            if e_param up || e_sf_id up then ()
            else type_error (loc p)
                 ("Parameters to subfunctionalities can be either " ^
                  "parameters of functionality or other subfunctionalities. " ^
                  up ^ " is neither."))
         sf.fun_param_ids)
   else type_error (loc sf.fun_id)
        ("Nonexisting functionality : " ^ fun_id);
   mk_loc (loc sf.id) {fun_id = fun_id; fun_param_ids = sf.fun_param_ids})

let check_exactly_one_initial_state (id : id) (sds : state_def list) : id = 
  let inits =
        List.filter
        (fun sd ->
           match sd with
           | InitialState _ -> true
           | _              -> false)
        sds in
  match List.length inits with
  | 0 -> type_error (loc id) ((unloc id) ^ " doesn't have initial state")
  | 1 ->
      (match List.hd inits with
       | InitialState s   -> s.id
       | FollowingState _ ->
           raise (Failure "impossible, list contains only InitialState"))
  | _ -> type_error (loc id) ((unloc id) ^ " has more than one initial state")

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
       mmcodes = s.code.mmcodes}
  | Some (id,t) ->
      type_error (loc t)
      ("Variable name " ^ id ^ " is the same as one of the states parameters.")
                        
let drop_state_ctor (sd : state_def) : state = 
  match sd with 
  | InitialState s   -> s
  | FollowingState s -> s

let check_states (id : id) (code : state_def list) : state_tyd IdMap.t = 
  let init_id = check_exactly_one_initial_state id code in
  let states = List.map (fun sd -> drop_state_ctor sd) code in
  let code_map = check_unique_id states (fun s -> s.id) in
  IdMap.map (check_state_decl init_id) code_map 

type b_io_path = (string list) * basic_io_body_tyd

type r_fb_io_paths =
  {direct : b_io_path list; adversarial : b_io_path list;
   internal : b_io_path list}

let getb_io_paths (root : string) (ioid : string) (ios : io_tyd IdMap.t) :
                  b_io_path list = 
  let getb_body (id : string) : basic_io_body_tyd = 
    let io = IdMap.find id ios in
    match (unloc io) with
    | Basic b -> b
    | _       ->
        raise (Failure
               "Cannot happen, this function is called only on Basic IOs") in
  let io = IdMap.find ioid ios in
  match (unloc io) with
  | Basic b       -> [([root],b)]
  | Composite cio ->
      IdMap.fold
      (fun id it l ->
         ([root; id], getb_body (unloc (unloc it))) :: l)
      cio []

let get_io_paths (ioid : string) (ios : io_tyd IdMap.t) : string list list = 
  let bps = getb_io_paths ioid ioid ios in
  List.map (fun bp -> fst bp) bps

let get_fun_io_paths (id_dir_io : string) (id_adv_io : string option)
                     (dir_ios : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t) :
      string list list = 
  let dir = get_io_paths id_dir_io dir_ios in
  let adv =
        match id_adv_io with
        | Some id -> get_io_paths id adv_ios
        | None    -> [] in
  dir @ adv

let check_i_opath (id_dir_io : string) (id_adv_io : string option)
                  (dir_ios : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t)
                  (iop : id list) : string list located = 
  let uiop = unlocs iop in
  let loc = mergelocs iop in
  let ps = get_fun_io_paths id_dir_io id_adv_io dir_ios adv_ios in
  if (List.mem uiop ps) then mk_loc loc uiop
  else let psf = List.filter (fun p -> (List.tl p) = uiop) ps in
       match (List.length psf) with
       | 0 ->
           type_error loc
           (string_of_i_opath uiop ^
            " is not a part of the interfaces implemented by functionality.")
       | 1 -> mk_loc loc (List.hd psf)
       | _ ->
           type_error loc
           (string_of_i_opath uiop ^
            " is ambiguous, it is in both direct and adversarial IOs " ^
            "implemented by functionality.")

let check_served_paths (serves : string list located list)
                       (id_dir_io : string) (pid : id) : unit = 
  let er =
        ("A party can serve at most one basic direct IO and one " ^
         "basic adversarial IO.") in
  let erone = "A party must serve one basic direct IO." in
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
      then type_error (loc iop) ("Parties must serve distinct IOs")
      else uiop :: l)
   [] iops)

let check_ios_cover (id_dir_io : string) (id_adv_io : string option)
                     (dir_ios : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t)
                     (served_ps : string list located list) : unit = 
  let serps = unlocs served_ps in
  let ps = get_fun_io_paths id_dir_io id_adv_io dir_ios adv_ios in
  let unserved = List.filter (fun p -> not (List.mem p serps)) ps in
  if (List.length unserved) = 0 then ()
  else type_error
       (mergelocs served_ps)
       ("These IOs are not served by any party : " ^
        (string_of_i_opaths unserved))

let check_party_decl (id_dir_io : string) (id_adv_io : string option)
                     (dir_ios : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t)
                     (p : party_def) : party_def_tyd = 
  let serves =
        List.map
        (check_i_opath id_dir_io id_adv_io dir_ios adv_ios)
        p.serves in
  let () = check_served_paths serves id_dir_io p.id in
  let code = check_states p.id p.code in
  mk_loc (loc p.id) {serves = serves; code = code}

let check_parties_serve_direct_sum (parties : party_def_tyd IdMap.t)
      (id_dir_io : string) (id_adv_io : string option)
      (dir_ios : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t) : unit = 
  let served_ps =
        IdMap.fold (fun _ p l -> l @ (unloc p).serves) parties [] in
  let () = check_ios_unique served_ps in
  check_ios_cover id_dir_io id_adv_io dir_ios adv_ios served_ps

let get_real_fun_sub_item_id (si : sub_item) : id = 
  match si with
  | SubFunDecl sf -> sf.id
  | PartyDef p    -> p.id

let check_exists_dir_io (dir_ios : io_tyd IdMap.t) (id_dir_io : id) = 
  let uid_dir_io = unloc id_dir_io in
  if exists_id dir_ios uid_dir_io then () 
  else type_error (loc id_dir_io)
                  ("direct_io " ^ uid_dir_io ^ " doesn't exist.")

let check_exists_i2_sio (i2s_ios : io_tyd IdMap.t) (id_i2_sio : id) = 
  let uid_i2_sio = unloc id_i2_sio in
  if exists_id i2s_ios uid_i2_sio
  then match unloc (IdMap.find uid_i2_sio i2s_ios) with
       | Basic _     -> ()
       | Composite _ ->
           type_error (loc id_i2_sio)
           "This adversarial_io cannot be composite."
        else type_error (loc id_i2_sio)
             ("adversarial_io " ^ uid_i2_sio ^ " doesn't exist.")

let check_fun_decl (e_f_id:string->bool) (dir_ios:io_tyd IdMap.t)
                   (adv_ios:io_tyd IdMap.t) (r_fun:fun_def) : fun_tyd =
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
                  ("adversarial_io "^uid^" doesn't exist.")) in
  let sub_items = check_unique_id r_fun.body get_real_fun_sub_item_id in
  let () =
    let dup_ids = IdMap.filter (fun id _ -> IdMap.mem id params) sub_items in
    if IdMap.is_empty dup_ids then ()
    else let id, dup = IdMap.choose dup_ids in
         let lc=loc (get_real_fun_sub_item_id dup) in
         type_error lc
         ("The name " ^ id ^
          " is the same name as one of the functionalities parameters.") in
   let sf_map =
         filter_map
         (fun sub_i ->
                match sub_i with
                | SubFunDecl sf -> Some sf
                | _ -> None)
         sub_items in
   let e_param = exists_id params and e_sf_id = exists_id sf_map in
   let sub_funs =
         IdMap.map (check_sub_fun_decl e_f_id e_param e_sf_id) sf_map in
   let () = check_is_composite dir_ios r_fun.id_dir in
   let (parties, states) =
         if r_fun.state_body = []
         then let () =
                    match r_fun.id_adv with
                    | Some id -> check_is_composite adv_ios id
                    | _       -> () in
               let p_map =
                     filter_map
                     (fun sub_i ->
                            match sub_i with
                            | PartyDef p -> Some p
                            | _ -> None)
                     sub_items in
               let ps =
                     IdMap.map
                     (check_party_decl id_dir_io id_adv_io dir_ios adv_ios)
                     p_map in
               (check_parties_serve_direct_sum ps id_dir_io id_adv_io
                dir_ios adv_ios;
                (ps, IdMap.empty))
         else match r_fun.id_adv with
              | None ->
                  type_error (loc r_fun.id)
                  ("A functionality with no parties must implement " ^
                   "a basic adversarial interface")
              | Some id ->
                  (check_exists_i2_sio adv_ios id;
                   let ss = check_states r_fun.id r_fun.state_body in
                   (IdMap.empty, ss)) in
   mk_loc (loc r_fun.id)
          {params = params; id_dir_io = id_dir_io; id_adv_io = id_adv_io;
           sub_funs = sub_funs; parties = parties; states = states}

let get_dir_io_id_impl_by_fun (fid : string) (funs : fun_tyd IdMap.t) :
                                string = 
  let r_f = IdMap.find fid funs in (unloc r_f).id_dir_io

let get_param_dir_io_ids (r_funs : fun_tyd IdMap.t) (rfid : string) :
                           string list = 
  unlocs (unlocs (to_list((unloc (IdMap.find rfid r_funs)).params)))

let check_sub_fun_params (funs : fun_tyd IdMap.t) : unit = 
  let get_dir_io_id rfid id =                
    let f = unloc (IdMap.find rfid funs) in
    let p = IdMap.find_opt id f.params in
    let s = IdMap.find_opt id f.sub_funs in
    match (p,s) with
    | (Some pm, None) -> unloc (unloc (fst pm))
    | (None, Some sf) -> get_dir_io_id_impl_by_fun ((unloc sf).fun_id) funs
    | _ ->
        raise (Failure ("Impossible - we already checked that sub_fun " ^
                        "params exist and are unique in check_sub_fun_decl")) in
  let get_dir_io_ids rfid ids =
    List.map (fun id -> get_dir_io_id rfid id) ids in
  let check_sf_ps rfid sf = 
    let usf = unloc sf in
    let sfps = get_param_dir_io_ids funs usf.fun_id in
    let sfpids = unlocs usf.fun_param_ids in
    let sfps' = get_dir_io_ids rfid sfpids in
    if List.length sfps <> List.length sfps'
      then type_error (loc sf)
                      ("Wrong number of parameters for subfunctionality")
    else if sfps <> sfps'
      then type_error (loc sf)
                      ("Parameter provided to subfunctionality " ^
                       "implement different direct_ios from " ^
                       "declared parameters.")
      else true in
  ignore
  (IdMap.for_all 
   (fun idrf rf ->
          IdMap.for_all 
          (fun _ sf -> check_sf_ps idrf sf)
          (unloc rf).sub_funs)
   funs)

type state_vars =
  {flags : string list; internal_ports : QidSet.t; consts : typ IdMap.t;
   vars : typ IdMap.t; initialized_vs : IdSet.t}

let init_state_vars (s : state_body) (ports : QidSet.t)
                    (flags : string list) : state_vars = 
  let consts = IdMap.map (fun p -> fst (unloc p)) s.params in
  let vars = IdMap.map (fun v -> unloc v) s.vars in
  {flags = flags; internal_ports = ports; consts = consts;
   vars = vars; initialized_vs = IdSet.empty}

type state_sig = typ list option

let get_state_sig (s : state_body) : state_sig = 
  if s.is_initial then None
  else let ps = IdMap.bindings s.params in
       let ts = unlocs (snd (List.split ps)) in
       let tord = List.sort (fun t1 t2 -> snd t1 - snd t2) ts in
       Some (fst (List.split tord))

let get_state_sigs (states : state_tyd IdMap.t) : state_sig IdMap.t = 
  IdMap.map (fun s -> get_state_sig (unloc s) ) states

let string_of_msg_path (mp : msg_path) : string = 
  let siop = string_of_i_opath (unlocs mp.io_path) in
  match mp.msg_type with 
  | MsgType id -> siop ^ "." ^ (unloc id)
  | OtherMsg _ -> siop ^ ".othermsg"

let string_of_msg_pathl (mpl : msg_path list) : string = 
  string_of_stringl (List.map (fun mp -> string_of_msg_path mp) mpl)

let filterb_io_ps (dir : msg_dir) (biops : b_io_path list) :
                    b_io_path list = 
  List.map
  (fun biop ->
         (fst biop,
          IdMap.filter
          (fun _ md -> (unloc md).direction = dir)
          (snd biop)))
  biops

let get_incoming_msg_paths (bps : r_fb_io_paths) : r_fb_io_paths = 
  { direct = filterb_io_ps In bps.direct;
    adversarial = filterb_io_ps In bps.adversarial;
    internal = filterb_io_ps Out bps.internal }

let get_outgoing_msg_paths (bps : r_fb_io_paths) : r_fb_io_paths = 
  { direct = filterb_io_ps Out bps.direct;
    adversarial = filterb_io_ps Out bps.adversarial;
    internal = filterb_io_ps In bps.internal }

let msg_loc (mp : msg_path) : EcLocation.t = 
  match mp.msg_type with
  | MsgType id -> loc id
  | OtherMsg l -> l

let msg_paths_of_b_io_path (bp : b_io_path) : msg_path list =   
  IdMap.fold
  (fun id _ l ->
         { io_path = dummylocl (fst bp);
           msg_type = MsgType (dummyloc id) } :: l)
  (snd bp) []

let mp_of_bpl (bpl : b_io_path list) : msg_path list = 
  List.flatten (List.map (fun bp -> msg_paths_of_b_io_path bp) bpl)

let flatten_r_fb_io_paths (bps : r_fb_io_paths) : b_io_path list = 
  bps.direct @ bps.adversarial @ bps.internal

let msg_paths_of_r_fb_io_paths (bps : r_fb_io_paths) : msg_path list = 
  mp_of_bpl (flatten_r_fb_io_paths bps)

let check_msg_path (bps : r_fb_io_paths) (mp : msg_path) : msg_path = 
  let ips = mp_of_bpl bps.internal in
  let allps = msg_paths_of_r_fb_io_paths bps in       
  let filter_by_msg_type (mt : id) (mpl : msg_path list) : msg_path list = 
    List.filter
    (fun p ->
           match p.msg_type with
           | MsgType mt' -> (unloc mt') = (unloc mt)
           | _           -> false)
    mpl in
  let filter_by_port_name_msg_type (pt : id) (mt : id)
                                   (mpl : msg_path list) : msg_path list = 
    filter_by_msg_type mt
    (List.filter
     (fun p ->
            unloc (List.hd(List.rev p.io_path)) = unloc pt)
     mpl) in
  let unexpected() = 
    type_error (msg_loc mp)
               ("The message is unexpected. These messages are expected : " ^
                string_of_msg_pathl allps) in
  let ambiguous (mtch : msg_path list) = 
    type_error (msg_loc mp)
               ("The message is ambiguous. There are multiple messages " ^
                "that match the description : " ^ string_of_msg_pathl mtch) in
  let filtered (mtch : msg_path list) (imtch : msg_path list) : msg_path = 
    match List.length mtch with
    | 0 -> unexpected ()
    | 1 ->
        let l = merge (mergelocs mp.io_path) (msg_loc mp) in
        if imtch = []
        then let ret = List.hd mtch in
               {io_path =
                  List.map
                  (fun id -> mk_loc l (unloc id))
                  ret.io_path;
                msg_type = mp.msg_type }
        else type_error l
                        ("Internal messages must have full paths. " ^
                         "Did you mean " ^ (string_of_msg_path (List.hd mtch)) ^
                          " ?")
    | _ -> ambiguous mtch in
  match mp.msg_type with
  | MsgType mt -> 
      if List.exists
         (fun p -> string_of_msg_path p = string_of_msg_path mp)
         allps
      then mp
      else (match (List.length mp.io_path) with
            | 0 -> let filter = filter_by_msg_type mt in
                   let mtch = filter allps in
                   let imtch = filter ips in
                   filtered mtch imtch
            | 1 -> let filter =
                     filter_by_port_name_msg_type (List.hd mp.io_path) mt in
                   let mtch = filter allps in
                   let imtch = filter ips in
                   filtered mtch imtch
            | _ ->  unexpected ())
  | OtherMsg _ ->
      if (List.exists
          (fun p -> qid1_starts_with_qid2 p.io_path mp.io_path)
          allps)
      then mp else unexpected ()

let remove_covered_paths (mps : msg_path list) (mp : msg_path) :
                           msg_path list = 
  let covered mp1 mp2 = 
    match mp2.msg_type with
    | MsgType _  -> string_of_msg_path mp1 = string_of_msg_path mp2
    | OtherMsg _ -> qid1_starts_with_qid2 mp1.io_path mp2.io_path in
  let rem = List.filter (fun mp' -> not (covered mp' mp) ) mps in
  if List.length mps = List.length rem
  then type_error (msg_loc mp)
       ("This match is covered by previous matches and would never execute.")
  else rem

let msg_paths_of_r_fb_io_paths_w_othermsg (bps : r_fb_io_paths) :
                                            msg_path list = 
  let mps = msg_paths_of_r_fb_io_paths bps in
  let omps =
        List.map
        (fun bp ->
             { io_path = dummylocl (fst bp);
               msg_type = OtherMsg _dummy })
        (flatten_r_fb_io_paths bps) in
  mps @ omps

let check_mm_ds_non_empty (bps : r_fb_io_paths) (mpl : msg_path list) :
                            msg_path list = 
  let mps = msg_paths_of_r_fb_io_paths_w_othermsg bps in
  List.fold_left (fun mps mp -> remove_covered_paths mps mp) mps mpl

let check_msg_match_deltas (rfbps : r_fb_io_paths) (mml : msg_match list) :
                             unit = 
  let mps = get_incoming_msg_paths rfbps in
  let r =
        check_mm_ds_non_empty
        mps (List.map (fun (mm : msg_match) -> mm.path) mml) in
  if r<>[]
  then let l = msg_loc ((List.hd (List.rev mml)).path)
       in type_error l
                     ("Message match is not exhaustive, these " ^
                      "messages are not matched : " ^
                      string_of_msg_pathl r)
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
         raise (Failure
                ("Impossible, we already checked params and local " ^
                 "vars have different ids")))
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
       (uvid ^ " is not a local variable and values cannot be bound to it.")
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
  then type_error (loc cid) (ucid ^ " is already used.")
  else {flags = sv.flags; internal_ports = sv.internal_ports;
        consts = IdMap.add ucid ct sv.consts; vars = sv.vars;
        initialized_vs = sv.initialized_vs}

let check_port_var_binding (bps : r_fb_io_paths) (mp : string list)
                           (vid : id) (sv : state_vars) : state_vars = 
  let d = List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.direct in
  let i =
    List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.internal in
  let a =
    List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.adversarial in
  if not (d && not i && not a)
  then type_error (loc vid)
       ("The message " ^ string_of_i_opath mp ^
        " maybe isn't an incoming message of a direct_io served by the " ^
        "party and cannot bind the source port to a variable.")
  else check_add_const vid port_type port_type sv

let check_item_type_add_binding (sv : state_vars) (mi : match_item)
                                (typ : typ) : state_vars = 
  match mi with
  | Wildcard _   -> sv
  | Const id     -> check_add_const id typ typ sv
  | ConstType nt -> check_add_const nt.id (check_type nt.ty) typ sv

let rec get_loc_ty (ty : ty) : EcLocation.t = 
  match ty with
  | NamedTy id -> loc id
  | TupleTy tl -> mergeall (List.map (fun t -> get_loc_ty t) tl)

let get_loc_match_item (m_i : match_item) : EcLocation.t = 
  match m_i with
  | Wildcard l   -> l
  | Const id     -> loc id
  | ConstType nt -> merge (loc nt.id) (get_loc_ty nt.ty)

let get_loc_match_item_list (tm : match_item list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_match_item mi) tm)

let check_msg_content_bindings (ps : b_io_path list) (mp : string list*string)
                               (tm : match_item list) (sv : state_vars) :
                                 state_vars = 
  let p = List.find (fun p -> (fst p) = (fst mp)) ps in
  let mt = to_list (unlocm((unloc(IdMap.find (snd mp) (snd p))).content)) in
  if List.length mt <> List.length tm
  then type_error (get_loc_match_item_list tm)
                  ("The number of bindings is different then the number " ^
                   "of message parameters.")
  else List.fold_left2 check_item_type_add_binding sv tm mt

let check_tuple_match (bps : b_io_path list) (mm : msg_match)
                      (sv : state_vars) : state_vars = 
  match mm.tuple_match with
  | None     -> sv
  | Some mil -> 
      match mm.path.msg_type with
      | OtherMsg l ->
          type_error l
                     ("othermsg cannot have value bindings. Do you have " ^
                      "redundant parenthesis?")
      | MsgType id ->
          check_msg_content_bindings bps
          ((unlocs mm.path.io_path),(unloc id)) mil sv

let check_match_bindings (bps : r_fb_io_paths) (mm : msg_match)
                         (sv : state_vars) : state_vars = 
  let sv' =        
    match mm.port_var with
    | Some id -> check_port_var_binding bps (unlocs mm.path.io_path) id sv
    | None    -> sv in
  let ps = bps.direct@bps.adversarial@bps.internal in
  check_tuple_match ps mm sv'

let get_var_type (sv : state_vars) (id : id) : typ = 
  let vs =
    IdMap.union
    (fun _ _ ->
           raise (Failure
                  ("Impossible! we already checked that params and " ^
                   "vars have different names")))
    sv.consts sv.vars in
  IdMap.find (unloc id) vs

let check_initialized (sv : state_vars) (id : id) : unit = 
  let uid = unloc id in
  if IdMap.mem uid sv.consts || IdSet.mem uid sv.initialized_vs then ()
  else type_error (loc id) (uid ^ " is not initialized.")    

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
  then type_error (loc ex) ("You can sample only from distributions.")
  else let dtyp = UcExpressions.get_distribution_typ etyp in 
       check_type_add_binding vid dtyp sv

let check_transition (si : state_instance) (ss : state_sig IdMap.t)
                     (sv : state_vars) : unit = 
  let ssig = 
    try IdMap.find (unloc(si.id)) ss with
      Not_found ->
        type_error (loc si.id) ("Non-existing state : " ^ (unloc si.id)) in
  match ssig, si.params with
  | None, None   -> ()
  | None, Some _ ->
      type_error (loc si.id)
      "State doesn't have parameters, do you have reduntant parentheses?"
  | Some _, None ->
      type_error (loc si.id) "State has parameters, none are provided."
  | Some sp, Some params -> 
      if List.length sp <> List.length params
      then type_error (loc si.id) "Wrong number of parameters."
      else let te = List.combine sp params in
           List.iteri
           (fun i (sigt,sip) -> 
                  let et = check_expression sv sip in
                  if sigt <> et && sigt<>univ_type
                  then type_error (loc sip)
                       (string_of_int (i+1) ^ ". parameter of state " ^
                        unloc si.id ^ " has type " ^ string_of_typ sigt ^
                        ", which is incompatible with provided type " ^
                        string_of_typ et)
                  else ())
           te

let check_msg_content_values (es : expression_l list) (mc : typ_tyd IdMap.t)
                             (sv : state_vars) : unit = 
  let sg = to_list (unlocm mc) in
  let esl = mergelocs es in
  if List.length es <> List.length sg
  then type_error esl "Parameter number mismatch."
  else List.iter2
       (fun ex typ ->
              if not (check_expression sv ex = typ)
              then type_error (loc ex) ("Parameter type mismatch"))
       es sg

let check_send_direct (msg : msg_instance) (mc : typ_tyd IdMap.t)
                      (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_var with
    | Some p ->
        (check_exists_and_has_compatible_type p port_type sv;
         check_initialized sv p)
    | None   -> type_error l ("Missing destination port.") in
  check_msg_content_values msg.tuple_instance mc sv

let check_send_adversarial (msg : msg_instance) (mc : typ_tyd IdMap.t)
                           (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_var with
    | Some _ ->
        type_error l "Only direct messages can have destination port."
    | None   -> () in
  check_msg_content_values msg.tuple_instance mc sv

let check_send_internal (msg : msg_instance) (mc : typ_tyd IdMap.t)
                        (sv : state_vars) : unit = 
  let l = msg_loc msg.path in
  let () =
    match msg.port_var with
    | Some _ ->
        type_error l
                   ("Messages to subfunctionalities cannot have " ^
                    "destination port.")
    | None -> () in
  check_msg_content_values msg.tuple_instance mc sv

let is_msg_path_inb_io_paths (mp : msg_path) (bps : b_io_path list) : bool = 
  let bpo = List.find_opt (fun bp -> fst bp = unlocs mp.io_path) bps in
  match bpo with
  | Some _ -> true
  | None   -> false

let get_msg_def_for_msg_path (mp : msg_path) (bs : b_io_path list) :
                               message_def_body = 
  let iop = unlocs mp.io_path in
  let bio = List.find (fun bp -> (fst bp) = iop) bs in
  let mt  =
    match mp.msg_type with
    | MsgType id -> unloc id
    | OtherMsg _ ->
        raise (Failure "OtherMsg doesn't have definition in interface") in
  let mdb = IdMap.find mt (snd bio) in
  unloc mdb

let check_send_msg_path (msg : msg_instance) (bps : r_fb_io_paths)
                        (sv : state_vars) : msg_instance = 
  let ps = get_outgoing_msg_paths bps in
  let path' = check_msg_path ps msg.path in
  let msg' =
    {path = path'; tuple_instance = msg.tuple_instance;
     port_var = msg.port_var} in
  let () =
    if List.mem "simulator" sv.flags && msg.path <> msg'.path
    then type_error (msg_loc msg.path)
         ("Messages sent by simulator must have complete path, did you mean " ^
          string_of_msg_path msg'.path ^ " ?")
    else () in
  msg'

let check_send (msg : msg_instance) (bps : r_fb_io_paths)
               (sv : state_vars) : msg_instance = 
  let msg' = check_send_msg_path msg bps sv in
  let bs = bps.direct@bps.adversarial@bps.internal in
  let mdbc = (get_msg_def_for_msg_path msg'.path bs).content in
  let () =
    match msg'.path with
    | ( _ as p) when is_msg_path_inb_io_paths p bps.direct ->
        check_send_direct msg' mdbc sv
    | ( _ as p) when is_msg_path_inb_io_paths p bps.adversarial ->
        check_send_adversarial msg' mdbc sv
    | ( _ as p) when is_msg_path_inb_io_paths p bps.internal ->
        check_send_internal msg' mdbc sv
    | _ ->
        raise (Failure
               ("impossible - the path is always in one of direct|" ^
                "adversarial|internal")) in
  msg'

let check_send_and_transition (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
                              (sat : send_and_transition) (sv : state_vars) :
                                instruction = 
  let msg' = check_send sat.msg bps sv in
  let () = check_transition sat.state ss sv in
  SendAndTransition {msg = msg'; state = sat.state}

let merge_state_vars (sv1 : state_vars) (sv2 : state_vars) : state_vars = 
  {flags = sv1.flags; internal_ports = sv1.internal_ports;
   consts = sv1.consts; vars = sv1.vars;
   initialized_vs = IdSet.inter sv1.initialized_vs sv2.initialized_vs}

let rec check_ite (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
                  (sv : state_vars) (ex : expression_l)
                  (tins : instruction_l list)
                  (eins : instruction_l list option) :
                    instruction*state_vars = 
  if check_expression sv ex <> bool_type
  then type_error (loc ex) "The condition must be a boolean expression."
  else let (tins_c, eins_c, sv') = check_branches bps ss sv tins eins in
       (ITE (ex, tins_c, eins_c), sv')

and check_branches (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
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

and check_decode (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
                 (sv : state_vars) (ex : expression_l) (ty : ty)
                 (m_is : match_item list) (okins : instruction_l list)
                 (erins : instruction_l list) : instruction * state_vars = 
  if check_expression sv ex <> univ_type
  then type_error (loc ex) "Only expressions of univ type can be decoded."
  else let dt =
         match check_type ty with
         | Tconstr (x, y) -> [Tconstr (x,y)]
         | Ttuple  t      -> t
         | _              ->
             raise (Failure
                    ("check_type is supposed to return only " ^
                    "Tconstr or Ttuple.")) in
       if List.length m_is <> List.length dt
       then type_error (get_loc_match_item_list m_is)
            ("The number of bindings is different from the arity of " ^
             "decoded type.")
       else let sv' = List.fold_left2 check_item_type_add_binding sv m_is dt in
            let (okins_c, erins_c, sv'') =
              check_branches bps ss sv' okins (Some erins) in
            ((Decode (ex, ty, m_is, okins_c, Option.get erins_c)), sv'')

and check_instruction (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
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

and check_instructions (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
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
  | [] -> raise (Failure "the instruction list cannot be empty")
  | {pl_loc = _; pl_desc = (SendAndTransition _)} :: [] -> ()
  | {pl_loc = l; pl_desc = (SendAndTransition _)} :: _ :: _ ->
      type_error l
                 ("The instructions after send and transition will " ^
                  "not be executed")
  | {pl_loc = _; pl_desc = Fail} :: [] -> ()
  | {pl_loc = l; pl_desc = Fail} :: _ :: _ ->
      type_error l ("The instructions after fail will not be executed")
  | {pl_loc = _; pl_desc = (ITE (_,tins,Some eins))} :: [] ->
      (check_ends_are_sa_tor_f tins; check_ends_are_sa_tor_f eins)
  | {pl_loc = _; pl_desc = (ITE (_,tins,Some eins))} :: ins :: _
      when (contains_sa_tor_f tins)&&(contains_sa_tor_f eins) ->
      type_error (loc ins)
                 ("The instructions after if-then-else will not be " ^
                  " executed since both branches contain send and " ^
                  "transition or fail commands.")
  | {pl_loc = _; pl_desc = (Decode (_,_,_,okins,erins))} :: [] ->
      check_ends_are_sa_tor_f okins; check_ends_are_sa_tor_f erins
  | {pl_loc = _; pl_desc = (Decode (_,_,_,okins,erins))} :: ins :: _
      when contains_sa_tor_f okins && contains_sa_tor_f erins ->
      type_error (loc ins)
                 ("The instructions after decode will not be executed " ^
                  "since both branches contain send and transition or " ^
                  "fail commands.")
  | ins :: [] ->
      type_error (loc ins)
                 ("Every branch of execution must end with send and " ^
                  "transition or fail command.")
  | _ :: tl -> check_ends_are_sa_tor_f tl

let check_msg_code (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
                   (sv : state_vars) (is : instruction_l list) :
                     instruction_l list = 
  let is_tyd = fst (check_instructions bps ss sv is) in
  let () = check_ends_are_sa_tor_f is_tyd in
  is_tyd

let check_message_path (bps : r_fb_io_paths) (mmc : msg_match_code) :
                         msg_match_code = 
  let path' =
    check_msg_path (get_incoming_msg_paths bps) mmc.pattern_match.path in
  {pattern_match = {port_var = mmc.pattern_match.port_var;
   path = path'; tuple_match = mmc.pattern_match.tuple_match};
   code = mmc.code}

let check_m_mcode (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
                  (sv : state_vars) (mmc : msg_match_code) : msg_match_code = 
  let mmc' = check_message_path bps mmc in 
  let sv' = check_match_bindings bps mmc'.pattern_match sv in
  let code' = check_msg_code bps ss sv' mmc'.code in
  {pattern_match = mmc'.pattern_match; code = code'}

let check_state_code (bps : r_fb_io_paths) (ss : state_sig IdMap.t)
                     (sv : state_vars) (mmcodes : msg_match_code list) :
                       msg_match_code list = 
  let mmcodes' = List.map (fun mmc -> check_m_mcode bps ss sv mmc) mmcodes in
  let () =
    check_msg_match_deltas bps
    (List.map (fun mmc -> mmc.pattern_match) mmcodes') in
  mmcodes'

let get_keys (m : 'a IdMap.t) : QidSet.t = 
  let lp = fst(List.split (IdMap.bindings m)) in
  List.fold_left (fun s p -> QidSet.add [p] s) QidSet.empty lp

let get_internal_ports (r_f : fun_body) : QidSet.t = 
  QidSet.union
  (get_keys r_f.parties)
  (QidSet.union (get_keys r_f.params) (get_keys r_f.sub_funs))

let filterb_io_paths (bps : b_io_path list) (pfxs : string list located list) :
                       b_io_path list = 
  List.filter
  (fun bp -> List.exists (fun pfx -> unloc pfx = fst bp) pfxs)
  bps

let get_fb_io_paths (dir_ios : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t)
                    (f : fun_tyd) : r_fb_io_paths = 
  let uf = unloc f in
  let iddir = uf.id_dir_io in
  let direct = getb_io_paths iddir iddir dir_ios in
  let adversarial = 
    match uf.id_adv_io with
    | Some id -> getb_io_paths id id adv_ios
    | None -> [] in
  {direct = direct; adversarial = adversarial; internal = []}

let get_r_fb_io_paths (dir_ios : io_tyd IdMap.t)
                      (adv_ios : io_tyd IdMap.t)
                      (funs : fun_tyd IdMap.t) (r_f : fun_tyd)
                      (p : party_def_tyd) : r_fb_io_paths = 
  let all = get_fb_io_paths dir_ios adv_ios r_f in
  let ur_f = unloc r_f in
  let filt = (unloc p).serves in
  let direct =  filterb_io_paths all.direct filt in
  let adversarial = filterb_io_paths all.adversarial filt in
  let internal_sfm =
    IdMap.mapi
    (fun sfid (sf : sub_fun_decl_tyd) ->
           let did = get_dir_io_id_impl_by_fun ((unloc sf).fun_id) funs in
           getb_io_paths sfid did dir_ios)
    ur_f.sub_funs in
  let internal_pm =
    IdMap.mapi
    (fun pid p -> 
           let did = unloc (unloc (fst p)) in
           getb_io_paths pid did dir_ios)
    ur_f.params in
  let internal_m =
    IdMap.union
    (fun _ _ _ ->
           raise (Failure
                  ("Impossible, we already checked params and " ^
                   "subfuns have different ids")))
    internal_sfm internal_pm in
  let internal = IdMap.fold (fun _ bps l -> l @ bps) internal_m [] in
  {direct = direct; adversarial = adversarial; internal = internal}

let check_state (ur_f : fun_body) (states : state_tyd IdMap.t)
                (bps : r_fb_io_paths) (s : state_tyd) : state_tyd = 
  let us = unloc s in
  let sv = init_state_vars (unloc s) (get_internal_ports ur_f) [] in
  let ss = get_state_sigs states in
  let mmcodes' = check_state_code bps ss sv us.mmcodes in
  mk_loc (loc s)
         {is_initial = us.is_initial; params = us.params; vars = us.vars;
          mmcodes = mmcodes'}

let check_party_code dir_ios adv_ios funs = 
  IdMap.map 
  (fun r_f -> 
         let ur_f = unloc r_f in 
         let parties = ur_f.parties in
         let parties' =
           IdMap.map 
           (fun p -> 
                  let up = unloc p in
                  let bps = get_r_fb_io_paths dir_ios adv_ios funs r_f p in
                  let states = up.code in
                  let states' =
                        IdMap.map (check_state ur_f states bps) states  in
                  mk_loc (loc p) {serves = up.serves; code = states'})
           parties in
         let states = ur_f.states in
         let bps = get_fb_io_paths dir_ios adv_ios r_f in
         let states' = IdMap.map (check_state ur_f states bps) states in
         mk_loc (loc r_f)
                {params = ur_f.params; id_dir_io = ur_f.id_dir_io;
                 id_adv_io = ur_f.id_adv_io; sub_funs = ur_f.sub_funs;
                 parties = parties'; states = states'})
  funs

let get_sf_refs_to_f_in_rf (funs : fun_tyd IdMap.t) (fid : string) : IdSet.t = 
  let rfb = IdMap.find fid funs in
  let sfrf =
    IdMap.filter
    (fun _ r -> exists_id funs (unloc r).fun_id)
    (unloc rfb).sub_funs in
  IdMap.fold (fun _ r set -> IdSet.add (unloc r).fun_id set) sfrf IdSet.empty

let check_circ_refs_in_r_funs (rfs : fun_tyd IdMap.t) =
  check_circ_refs get_sf_refs_to_f_in_rf rfs

let check_funs (fun_map : fun_def IdMap.t) (dir_ios : io_tyd IdMap.t)
               (adv_ios : io_tyd IdMap.t) : fun_tyd IdMap.t = 
  let e_f_id = exists_id fun_map in 
  let funs = IdMap.map (check_fun_decl e_f_id dir_ios adv_ios) fun_map in
  (check_circ_refs_in_r_funs funs;
   check_sub_fun_params funs;
   check_party_code dir_ios adv_ios funs)

(* Simulator checks *)

let check_msg_code_sim (fbps : r_fb_io_paths) (ss : state_sig IdMap.t)
                       (mmc : msg_match_code) (sv : state_vars) :
                         msg_match_code = 
  let code' = check_msg_code fbps ss sv mmc.code in
  {pattern_match = mmc.pattern_match; code = code'}

let check_message_path_sim (bps : b_io_path list) (isini : bool)
                           (mmc : msg_match_code) : unit = 
  let bps = filterb_io_ps In bps in
  let mp = mmc.pattern_match.path in
  let l = msg_loc mp in
  let id = fst (List.find (fun p -> (List.length (fst p)) = 1) bps) in
  if isini && unlocs mp.io_path <> id
  then type_error l
                  ("Initial state can handle only messages comming " ^
                   "from ideal functionality. Did you omit prefix " ^
                   List.hd id ^ ".?")
  else let iops = fst(List.split bps) in
       let invalid_dest() =
         type_error l
                    ("Not a valid destination, these destinations are " ^
                     "valid : " ^ string_of_i_opaths iops) in
       let umpiop = (unlocs mp.io_path) in
       match mp.msg_type with
       | MsgType mt ->
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
       | OtherMsg _ ->
           if List.exists
              (fun p -> sl1_starts_with_sl2 p umpiop)
              iops
           then ()
           else invalid_dest ()

let check_match_bindings_sim (bps : b_io_path list) (sv : state_vars)
                             (mmc : msg_match_code) : state_vars = 
  let mm = mmc.pattern_match in
  check_tuple_match bps mm sv

let check_msg_match_deltas_sim (rfbps : r_fb_io_paths)
                               (mmcodes : msg_match_code list) : unit = 
  let mps = get_incoming_msg_paths rfbps in
  ignore
  (check_mm_ds_non_empty mps
   (List.map
    (fun mmc ->
          {io_path = mmc.pattern_match.path.io_path;
           msg_type = mmc.pattern_match.path.msg_type})
    mmcodes))

let check_sim_state_code (bps : b_io_path list) (ss : state_sig IdMap.t)
                         (sv : state_vars) (isini : bool)
                         (mmcodes : msg_match_code list) :
                           msg_match_code list = 
  let () = List.iter (check_message_path_sim bps isini) mmcodes in
  let svs = List.map (check_match_bindings_sim bps sv) mmcodes in
  let fbps = {direct = []; adversarial = bps; internal = []} in
  let ret = List.map2 (check_msg_code_sim fbps ss) mmcodes svs in
  let () = check_msg_match_deltas_sim fbps ret in
  ret

(* TODO : fix this *)
let disj (_ : 'key) (_ : 'a) (_ : 'a) = 
  raise (Failure "Not disjoint!")

let disj_union (qml : 'a QidMap.t list) : 'a QidMap.t = 
  List.fold_left (fun qm1 qm2 -> QidMap.union disj qm1 qm2) QidMap.empty qml

let get_sim_components (funs : fun_tyd IdMap.t) (r_f : string)
                       (ps : string list) : fun_body QidMap.t = 
  let rec get_sc (funs : fun_tyd IdMap.t) (fid : string) (pfx : SL.t) :
                   fun_body QidMap.t = 
    if IdMap.mem fid funs
    then let urf = unloc(IdMap.find fid funs) in
         disj_union
         (QidMap.singleton pfx (urf) ::
          IdMap.fold
          (fun sfid sfd l ->
                 (get_sc funs (unloc sfd).fun_id (pfx @ [sfid])) :: l)
          urf.sub_funs [])
    else raise (Failure
                ("Impossible! We already checked that all referenced " ^
                 "functionalities exist")) in
  let urf = unloc(IdMap.find r_f funs) in
  let pids = IdMap.fold (fun pid _ l -> pid :: l) urf.params [] in
  let qpids = List.map (fun pid -> r_f :: [pid]) pids in
  disj_union(get_sc funs r_f [r_f] :: List.map2 (get_sc funs) ps qpids)
                
let get_component_io_paths (adv_ios : io_tyd IdMap.t) (f : fun_body) :
                             b_io_path list = 
  match f.id_adv_io with
  | Some id -> getb_io_paths id id adv_ios 
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

let invertb_i_ob_tyd (bio : basic_io_body_tyd) : basic_io_body_tyd = 
  IdMap.map invert_md_fl bio

let invert_msg_dirs (bp : b_io_path) : b_io_path = 
  let bio = snd bp in
  let bio' = invertb_i_ob_tyd bio in
  (fst bp, bio')

let get_simb_io_paths (adv_ios : io_tyd IdMap.t) (uses : string)
                      (cs : fun_body QidMap.t) : b_io_path list = 
  let sbps = QidMap.map (get_component_io_paths adv_ios) cs in        
  let bps =
    QidMap.add
    []
    (List.map
     (fun bp -> invert_msg_dirs bp)
     (getb_io_paths uses uses adv_ios))
    sbps in
  QidMap.fold
  (fun q bpl l ->
         l @ List.map (fun bp -> (q @ fst bp, snd bp)) bpl)
  bps []

let get_sim_internal_ports (cs : fun_body QidMap.t) : QidSet.t = 
  let rcsips = QidMap.map (fun fb -> get_internal_ports fb ) cs in
  let rcsqips =
    QidMap.mapi (fun q ips -> QidSet.map (fun ip -> q@ip) ips) rcsips in
  QidMap.fold (fun _ qips sip -> QidSet.union qips sip) rcsqips QidSet.empty
        
let check_sim_code (_ : io_tyd IdMap.t) (adv_ios : io_tyd IdMap.t)
                   (funs : fun_tyd IdMap.t) (sim : sim_def_tyd) : sim_def_tyd = 
  let usim = unloc sim in
  let states = usim.body in
  let ss = get_state_sigs states in
  let cs = get_sim_components funs usim.sims usim.sims_param_ids in
  let bps = get_simb_io_paths adv_ios usim.uses cs in
  let states' =
    IdMap.map 
    (fun s -> 
           let us = unloc s in
           let sv =
             init_state_vars us (get_sim_internal_ports cs) ["simulator"] in
           let mmcodes' =
             check_sim_state_code bps ss sv us.is_initial us.mmcodes in
           mk_loc (loc s)
                  {is_initial = us.is_initial; params = us.params;
                   vars = us.vars; mmcodes = mmcodes'})
    states in
  mk_loc (loc sim)
         {uses = usim.uses; sims = usim.sims;
          sims_param_ids = usim.sims_param_ids; body = states'}

let check_exists_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let urf = unloc rf in
  if exists_id funs urf then ()
  else type_error (loc rf) ("Functionality " ^ urf ^ " doesn't exist.")

let check_is_real_f (funs : fun_tyd IdMap.t) (rf : id) = 
  let () = check_exists_f funs rf in
  let f = unloc (IdMap.find (unloc rf) funs) in
  if f.parties = IdMap.empty
  then type_error (loc rf) ("The simulated functionality must have parties.")

let check_sim_fun_params (funs : fun_tyd IdMap.t) (_ : io_tyd IdMap.t)
                         (rf : id) (params : id list) = 
  let d_ios = get_param_dir_io_ids funs (unloc rf) in
  let d_ios' =
    List.map
    (fun id -> get_dir_io_id_impl_by_fun id funs) (unlocs params) in
  if List.length d_ios <> List.length d_ios'
  then type_error (loc rf)
                  ("Wrong number of parameters for functionality.")
  else let () =
         List.iteri
         (fun i pid ->
          if List.nth d_ios i <> List.nth d_ios' i
          then type_error (loc pid)
               ("Parameter implements different direct_io than required " ^
                "by functionality."))
         params in
       List.iter
       (fun pid ->
              let f = unloc (IdMap.find (unloc pid) funs) in
              if f.parties <> IdMap.empty
                 then type_error (loc pid)
                      ("The parameter to simulated functionality cannot " ^
                       "have parties")
                 else match f.id_adv_io with
                      | None ->
                          type_error (loc pid)
                          ("The parameter to simulated functionality " ^
                           "must implement an adversarial_io")
                      | Some _ -> () (* we already checked that it is *)
                        (* not composite when checking FunDecl for *)
                        (* partyless funs *))
       params

let check_sim_decl (_ : io_tyd IdMap.t) (i2s_ios : io_tyd IdMap.t)
                   (funs : fun_tyd IdMap.t) (sd : sim_def) : sim_def_tyd = 
  let () = check_exists_i2_sio i2s_ios sd.uses in
  let uses = unloc sd.uses in
  let () = check_is_real_f funs sd.sims in
  let sims = unloc sd.sims in
  let () = List.iter (check_exists_f funs) sd.sims_param_ids in
  let () = check_sim_fun_params funs i2s_ios sd.sims sd.sims_param_ids in
  let sims_param_ids = unlocs sd.sims_param_ids in
  let body = check_states sd.id sd.body in
  mk_loc (loc sd.id)
  {uses = uses; sims = sims; sims_param_ids = sims_param_ids; body = body}

let check_simulators (sim_map : sim_def IdMap.t) (dir_ios : io_tyd IdMap.t)
                     (adv_ios : io_tyd IdMap.t) (funs : fun_tyd IdMap.t) :
                       sim_def_tyd IdMap.t = 
  let sims = IdMap.map (check_sim_decl dir_ios adv_ios funs) sim_map in
  IdMap.map (check_sim_code dir_ios adv_ios funs) sims

(* DL prog checks *)

let get_io_id io_def = match io_def with
  | AdversarialIO io -> io.id
  | DirectIO io      -> io.id

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
         | None   -> raise (Failure "!impossible!"))
  flt

let check_defs def_l = 
  let def_map = check_unique_id def_l get_def_id in
  let dir_io_map =
    filter_map
    (fun def ->
           match def with
           | InterDef DirectIO io -> Some io
           | _ -> None)
    def_map in
  let adv_io_map =
    filter_map
    (fun def ->
           match def with
           | InterDef AdversarialIO io -> Some io
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
                 ("Error when require import-ing " ^ unloc idl ^ " : " ^ f) in
  List.iter reqimp reqs

let typecheck spec = 
  let () = UcEcInterface.init() in
  let () = load_ec_reqs spec.externals.ec_requirements in
  let ext_defs = load_uc_imports spec.externals.dl_imports in
  check_defs (ext_defs @ spec.definitions)
