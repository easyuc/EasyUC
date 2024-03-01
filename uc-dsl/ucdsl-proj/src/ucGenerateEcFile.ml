open UcTypedSpec

type maps_gen =
  {basic_dir_inter_map : string IdPairMap.t;  (* basic direct interfaces *)
   comp_dir_inter_map  : string IdPairMap.t;  (* composite direct interfaces *)
   basic_adv_inter_map : string IdPairMap.t;  (* basic adversarial interfaces *)
   comp_adv_inter_map  : string IdPairMap.t;  (* composite adversarial interfaces *)
   fun_map             : string IdPairMap.t;    (* functionalities *)
   sim_map             : string IdPairMap.t;
   uc_reqs_map         : (string list) IdMap.t; (* UC requires of roots *)
   ec_reqs_map   : ((string * bool) list) IdMap.t}

let gen_fun (id : string) (ft : fun_tyd) : string = ""
let gen_sim (id : string) (st : sim_tyd) : string = ""

let print_files (mg : maps_gen) : unit =
  let print_file (root : string) (mg : maps_gen) : unit =
    let fs = open_out ("UC__"^root^".eca") in
    
    let rdim_b = IdPairMap.filter (fun (r,_) _ -> r = root) mg.basic_dir_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rdim_b;
    let rdim_c = IdPairMap.filter (fun (r,_) _ -> r = root) mg.comp_dir_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rdim_c;

    let raim_b = IdPairMap.filter (fun (r,_) _ -> r = root) mg.basic_adv_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) raim_b;
    let raim_c = IdPairMap.filter (fun (r,_) _ -> r = root) mg.comp_adv_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) raim_c;

    let rootfun = IdPairMap.filter (fun (r,_) _ -> r = root) mg.fun_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rootfun

  in  
  let roots = 
    IdSet.union (roots_of_map mg.basic_dir_inter_map)
      (IdSet.union (roots_of_map mg.basic_adv_inter_map)
       (IdSet.union (roots_of_map mg.comp_dir_inter_map)
       (IdSet.union (roots_of_map mg.comp_adv_inter_map)
       (IdSet.union (roots_of_map mg.fun_map) (roots_of_map mg.sim_map))))) in
  IdSet.iter (fun r -> print_file r mg) roots

let generate_ec (mt : maps_tyd) : unit =
  let scope (root : string) =
    IdMap.find root mt.ec_scope_map
  in
  let f_is_int_basic = fun _ ibt -> is_basic_tyd (EcLocation.unloc ibt) in
  let mtdim_b, mtdim_c = IdPairMap.partition f_is_int_basic mt.dir_inter_map in
  let f_gen_int = fun sp it dim ->
      IdPairMap.add sp (
        UcGenerateInter.gen_int (scope (fst sp)) (fst sp) (snd sp) it
      ) dim in
  let dim_b = IdPairMap.fold f_gen_int mtdim_b IdPairMap.empty in
  let dim_c = IdPairMap.fold f_gen_int mtdim_c IdPairMap.empty in
  
  let mtaim_b, mtaim_c = IdPairMap.partition f_is_int_basic mt.adv_inter_map in
  let aim_b = IdPairMap.fold f_gen_int mtaim_b IdPairMap.empty in
  let aim_c = IdPairMap.fold f_gen_int mtaim_c IdPairMap.empty in

  let fm = IdPairMap.fold (fun sp ft fm -> IdPairMap.add
     sp (UcGenerateFunctionality.gen_fun (scope (fst sp)) (snd sp) ft
        ) fm
    ) mt.fun_map IdPairMap.empty in

  let sm = IdPairMap.fold
    (fun sp st sm ->
      IdPairMap.add sp (gen_sim (snd sp) st) sm
    ) mt.sim_map IdPairMap.empty in
  (*TODO handle uc_reqs and ec_reqs*)
  let mg =
    {basic_dir_inter_map = dim_b;
     comp_dir_inter_map  = dim_c;
     basic_adv_inter_map = aim_b;
     comp_adv_inter_map  = aim_c;
     fun_map       = fm;
     sim_map       = sm;
     uc_reqs_map   = mt.uc_reqs_map;
     ec_reqs_map   = mt.ec_reqs_map} in

  print_files mg
  (*TODO writing to the file + possible merging with already existing file*)
