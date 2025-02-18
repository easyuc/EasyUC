open UcTypedSpec
open UcGenerateCommon

type maps_gen =
  {basic_dir_inter_map : string IdPairMap.t;  (* basic direct interfaces *)
   comp_dir_inter_map  : string IdPairMap.t;  (* composite direct interfaces *)
   basic_adv_inter_map : string IdPairMap.t;  (* basic adversarial interfaces *)
   comp_adv_inter_map  : string IdPairMap.t;  (* composite adversarial interfaces *)
   fun_map             : string IdPairMap.t;  (* functionalities *)
   sim_map             : string IdPairMap.t;  (* simulators *)
   preamble_map        : string IdMap.t;}     (* UC and EC requires, port indices
                                                 and clones of subfunctionalities and parameter*)

let gen_sim (id : string) (st : sim_tyd) : string = ""

let print_files (mg : maps_gen) : unit =
  let print_file (root : string) (mg : maps_gen) : unit =
    let fs = open_out ((uc__name root)^".eca") in

    let pre = IdMap.find root mg.preamble_map in
    Printf.fprintf fs "%s" pre;
    
    let rdim_b = IdPairMap.filter (fun (r,_) _ -> r = root) mg.basic_dir_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rdim_b;
    let rdim_c = IdPairMap.filter (fun (r,_) _ -> r = root) mg.comp_dir_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rdim_c;

    let raim_b = IdPairMap.filter (fun (r,_) _ -> r = root) mg.basic_adv_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) raim_b;
    let raim_c = IdPairMap.filter (fun (r,_) _ -> r = root) mg.comp_adv_inter_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) raim_c;

    let rootfun = IdPairMap.filter (fun (r,_) _ -> r = root) mg.fun_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rootfun;

    let rootsim = IdPairMap.filter (fun (r,_) _ -> r = root) mg.sim_map in
    IdPairMap.iter (fun _ s -> Printf.fprintf fs "%s\n\n" s) rootsim

  in  
  let roots = 
    IdSet.union (roots_of_map mg.basic_dir_inter_map)
      (IdSet.union (roots_of_map mg.basic_adv_inter_map)
       (IdSet.union (roots_of_map mg.comp_dir_inter_map)
       (IdSet.union (roots_of_map mg.comp_adv_inter_map)
       (IdSet.union (roots_of_map mg.fun_map) (roots_of_map mg.sim_map))))) in
  IdSet.iter (fun r -> print_file r mg) roots

let print_preamble (mt : maps_tyd) (root : string) : string =
  let sf = Format.get_str_formatter () in
  let uc_reqs = IdMap.find(root) mt.uc_reqs_map in
  if List.is_empty uc_reqs  then () else
    Format.fprintf sf "@[require%a.@]@.@." (fun fs reqs->
       List.iter (fun s ->
         Format.fprintf sf "@ %s" (uc_name s)) reqs) uc_reqs;

  let ec_reqs = IdMap.find root mt.ec_reqs_map in
  let ec_req_imp, ec_req = List.partition (fun (s,b) -> b) ec_reqs in
  let ec_req_imp = List.filter (fun (s,_) -> s<>"UCBasicTypes") ec_req_imp in
  let print sf reqs = List.iter (fun (s,_) ->
                            Format.fprintf sf "@ %s" s) reqs
  in
  if List.is_empty ec_req_imp then () else
    Format.fprintf sf "@[require import%a.@]@.@." print ec_req_imp;
  
  if List.is_empty ec_req then () else
    Format.fprintf sf "@[require%a.@]@.@." print ec_req;

  Format.fprintf sf "require import UCCore.@.@.";

  Format.fprintf sf "require UCComposition.@.@.";

    let ui = unit_info_of_root mt root in
    begin match ui with
    | UI_Singleton _ ->
       Format.fprintf sf "op %s : int.@.@." adv_if_pi_op_name;
       Format.fprintf sf "axiom %s : 0 < %s.@.@."
         adv_if_pi_gt0_axiom_name adv_if_pi_op_name
    | UI_Triple ti    ->
       Format.fprintf sf "op %s : int.@.@." adv_pi_begin_op_name;
       Format.fprintf sf "axiom %s_gt0 : 0 < %s.@.@."
         adv_pi_begin_op_name adv_pi_begin_op_name;
       let rf = IdPairMap.find (root,ti.ti_real) mt.fun_map in
       let pinfo = get_info_of_real_func mt root 0 rf in
       IdMap.iter (fun ptname ptinfo ->
         match ptinfo.pi_pai with
         | None -> ()
         | Some  (_, _, _, ptadvpi) ->
            Format.fprintf sf "op %s = %s + %i.@."
              (adv_pt_pi_op_name ptname) adv_pi_begin_op_name ptadvpi
         ) pinfo;
       Format.fprintf sf "@.";
       let nsf = num_sub_funs_of_real_fun_tyd rf in
       for n = 0 to nsf-1 do
         let isf_name = sub_fun_name_nth_of_real_fun_tyd rf n in
         let isf_adv_pi = get_adv_pi_of_nth_sub_fun_of_real_fun
                            mt root 0 rf n in
         let sfnm = uc_name isf_name in
         let adv_pi_begin_str = adv_pi_begin_op_name^" + "^
                                  (string_of_int isf_adv_pi) in
         let root = fst (sub_fun_sp_nth_of_real_fun_tyd rf n) in
         clone_singleton_unit sf root sfnm adv_pi_begin_str
       done;
       Format.fprintf sf "@.op %s : int = %s.@.@."
         adv_if_pi_op_name adv_pi_begin_op_name;
       let np = num_params_of_real_fun_tyd rf in
       let papi : string ref = ref (string_of_int ti.ti_num_adv_pis) in
       for n = 0 to np-1 do
         let pname = param_name_nth_of_real_fun_tyd rf n in
         let r,_ = id_dir_inter_of_param_of_real_fun_tyd rf pname in
         let rui = unit_info_of_root mt r in
         let adv_pi_begin_str = adv_pi_begin_op_name^" + "^(!papi) in
         let ucpn = uc_name pname in
         let parampath = (uc_name pname)^"."^uc__code in
         match rui with
         | UI_Singleton _ ->
            clone_singleton_unit sf r ucpn adv_pi_begin_str;
            papi := !papi^" + 1"
         | UI_Triple _ ->
            let alias_apb = (adv_pi_begin_param pname) in
            Format.fprintf sf "op %s = %s.@.@."
              alias_apb adv_pi_begin_str;
            clone_triple_unit sf r ucpn alias_apb;
            papi := !papi^" + "^parampath^"."^adv_pi_num_op_name
       done;
       Format.fprintf sf "op %s : int = %s.@.@." adv_pi_num_op_name !papi
    end ;
  Format.flush_str_formatter ()


let dir_int_internals
(mt : maps_tyd) (root : string) (ft : fun_tyd) : symb_pair IdMap.t =
  let fbt = EcLocation.unloc ft in
  if is_ideal_fun_body_tyd  fbt
  then IdMap.empty
  else
    let rfbt = real_fun_body_tyd_of (EcLocation.unloc ft) in
    let bndgs = IdMap.bindings rfbt.sub_funs in
    let sf_nms = fst (List.split bndgs) in
    let pms = indexed_map_to_list_keep_keys rfbt.params in
    let pm_nms = fst (List.split pms) in
    let nms = sf_nms @ pm_nms in
    List.fold_left (fun ret nm ->
      let dir_int_sp = snd (EcUtils.oget
        (get_child_index_and_comp_inter_sp_of_param_or_sub_fun_of_real_fun
          mt root ft nm)) in
      IdMap.add nm dir_int_sp ret) IdMap.empty nms

let adv_int_simulated
(mt : maps_tyd) (root : string) (st : sim_tyd) : symb_pair IdPairMap.t =
  let sbt = EcLocation.unloc st in
  let ft = IdPairMap.find (root, sbt.sims) mt.fun_map in 
  let rfbt = real_fun_body_tyd_of (EcLocation.unloc ft) in
  let ret =
    if rfbt.id_adv_inter <> None
    then
      let rfaiid = EcUtils.oget rfbt.id_adv_inter in
      IdPairMap.add (sbt.sims, rfaiid) (root, rfaiid) IdPairMap.empty
    else
      IdPairMap.empty in
  let sf_nmifs = IdMap.bindings rfbt.sub_funs in
  let pms = indexed_map_to_list_keep_keys rfbt.params in
  let pm_nms = fst (List.split pms) in
  let pm_nmifs = List.combine pm_nms sbt.sims_arg_pair_ids in
  let nmifs = sf_nmifs @ pm_nmifs in
  List.fold_left (fun ret nmif ->
      let ifun = IdPairMap.find (snd nmif) mt.fun_map in
      let ifunu = EcLocation.unloc ifun in
      let ifbt = ideal_fun_body_tyd_of ifunu in
      let ifroot = fst (snd nmif) in
      if ifbt.id_adv_inter<>None
      then begin
        let adv_int_sp =  (ifroot, (EcUtils.oget ifbt.id_adv_inter)) in
        IdPairMap.add (sbt.sims,fst nmif) adv_int_sp ret
        end
      else
        ret
    ) ret nmifs
  

let generate_ec (mt : maps_tyd) : unit =
  let scope (root : string) =
    IdMap.find root mt.ec_scope_map
  in
  let roots = roots_of_maps mt in
  let preambles = IdSet.fold (fun root ps ->
    IdMap.add root (print_preamble mt root) ps ) roots IdMap.empty in
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

  let mbmap =  UcGenerateCommon.make_msg_path_map mt in

  let fm = IdPairMap.fold (fun sp ft fm ->
    let root, id = sp in
    let dii = dir_int_internals mt root ft in
    let rapm =
      if is_real_fun_tyd ft
      then Some (make_rf_addr_port_maps mt root ft)
      else None
    in
    let gvil =
      if is_real_fun_tyd ft
      then get_gvil mt sp 
      else empty_gvil
    in
    let pbs =
      if is_real_fun_tyd ft
      then get_parameter_bounds mt sp 
      else []                       
    in
    (*remove print
    let print_gvi (gvi : globVarId) : unit =
      print_endline "";
      List.iter (fun s -> print_string (s^".")) (fst gvi);
      print_string (snd gvi)
    in
    List.iter (fun gvi -> print_gvi gvi) gvil;
    print_endline "";
    end remove print*)
    IdPairMap.add      
    sp (UcGenerateFunctionality.gen_fun
          (scope root) root id mbmap rapm ft dii gvil pbs
    ) fm
    ) mt.fun_map IdPairMap.empty in

  let sm = IdPairMap.fold (fun sp st sm ->
    let root, id = sp in
    let ais = adv_int_simulated mt root st in           
    let sbt = EcLocation.unloc st in
    IdPairMap.add sp (UcGenerateFunctionality.gen_sim
                        (scope root) root id mbmap sbt ais) sm
    ) mt.sim_map IdPairMap.empty in
  let mg =
    {basic_dir_inter_map = dim_b;
     comp_dir_inter_map  = dim_c;
     basic_adv_inter_map = aim_b;
     comp_adv_inter_map  = aim_c;
     fun_map       = fm;
     sim_map       = sm;
     preamble_map  = preambles} in

  print_files mg
  
