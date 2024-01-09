open UcTypedSpec

type maps_gen =
  {dir_inter_map : string IdPairMap.t;  (* direct interfaces *)
   adv_inter_map : string IdPairMap.t;  (* adversarial interfaces *)
   fun_map       : string IdPairMap.t;    (* functionalities *)
   sim_map       : string IdPairMap.t}

let gen_dir_inter (id : string) (it : inter_tyd) : string =""
let gen_adv_inter (id : string) (it : inter_tyd) : string =""
let gen_fun (id : string) (ft : fun_tyd) : string = ""
let gen_sim (id : string) (st : sim_tyd) : string = ""

let print_files (mg : maps_gen) : unit = ()

let generate_ec (mt : maps_tyd) : unit =
  let dim = IdPairMap.fold
    (fun sp it dim ->
      IdPairMap.add sp (gen_dir_inter (snd sp) it) dim
    ) mt.dir_inter_map IdPairMap.empty in
  
  let aim = IdPairMap.fold
    (fun sp it aim ->
      IdPairMap.add sp (gen_adv_inter (snd sp) it) aim
    ) mt.adv_inter_map IdPairMap.empty in

  let fm = IdPairMap.fold
    (fun sp ft fm ->
      IdPairMap.add sp (gen_fun (snd sp) ft) fm
    ) mt.fun_map IdPairMap.empty in

  let sm = IdPairMap.fold
    (fun sp st sm ->
      IdPairMap.add sp (gen_sim (snd sp) st) sm
    ) mt.sim_map IdPairMap.empty in

  let mg =
    {dir_inter_map = dim;  (* direct interfaces *)
     adv_inter_map = aim;  (* adversarial interfaces *)
     fun_map       = fm;    (* functionalities *)
     sim_map       = sm } in

  print_files mg
  (*TODO writing to the file + possible merging with already existing file*)
