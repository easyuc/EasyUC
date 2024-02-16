open UcTypedSpec

type maps_gen =
  {dir_inter_map : string IdPairMap.t;  (* direct interfaces *)
   adv_inter_map : string IdPairMap.t;  (* adversarial interfaces *)
   fun_map       : string IdPairMap.t;    (* functionalities *)
   sim_map       : string IdPairMap.t;
   uc_reqs_map   : (string list) IdMap.t;           (* UC requires of roots *)
   ec_reqs_map   : ((string * bool) list) IdMap.t}

let gen_adv_inter (id : string) (it : inter_tyd) : string =""
let gen_fun (id : string) (ft : fun_tyd) : string = ""
let gen_sim (id : string) (st : sim_tyd) : string = ""

let print_files (mg : maps_gen) : unit =
  let print_file (root : string) (mg : maps_gen) : unit =
    let fs = open_out ("UC__"^root^".eca") in
    let rdim = IdPairMap.filter (fun (r,_) _ -> r = root) mg.dir_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rdim;
    let raim = IdPairMap.filter (fun (r,_) _ -> r = root) mg.adv_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) raim
  in
  let roots = 
    IdSet.union (roots_of_map mg.dir_inter_map)
    (IdSet.union (roots_of_map mg.adv_inter_map)
       (IdSet.union (roots_of_map mg.fun_map) (roots_of_map mg.sim_map))) in
  IdSet.iter (fun r -> print_file r mg) roots

let generate_ec (mt : maps_tyd) : unit =
  let scope (root : string) =
    IdMap.find root mt.ec_scope_map
  in
  let dim = IdPairMap.fold
    (fun sp it dim ->
      IdPairMap.add sp (
        UcGenerateInter.gen_int (scope (fst sp)) (fst sp) (snd sp) it
      ) dim
    ) mt.dir_inter_map IdPairMap.empty in
  
  let aim = IdPairMap.fold
    (fun sp it aim ->
      IdPairMap.add sp (
        UcGenerateInter.gen_int (scope (fst sp)) (fst sp) (snd sp) it
      ) aim
    ) mt.adv_inter_map IdPairMap.empty in

  let fm = IdPairMap.fold
    (fun sp ft fm ->
      IdPairMap.add sp (gen_fun (snd sp) ft) fm
    ) mt.fun_map IdPairMap.empty in

  let sm = IdPairMap.fold
    (fun sp st sm ->
      IdPairMap.add sp (gen_sim (snd sp) st) sm
    ) mt.sim_map IdPairMap.empty in
  (*TODO handle uc_reqs and ec_reqs*)
  let mg =
    {dir_inter_map = dim;
     adv_inter_map = aim;
     fun_map       = fm;
     sim_map       = sm;
     uc_reqs_map   = mt.uc_reqs_map;
     ec_reqs_map   = mt.ec_reqs_map} in

  print_files mg
  (*TODO writing to the file + possible merging with already existing file*)
