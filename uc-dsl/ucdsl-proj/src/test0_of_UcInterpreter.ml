open UcInterpreter

let rf0 = (("Root1","RF"), 1)
let rf1 = (("Root2","RF"), 10)
let rf2 = (("Root3","RF"), 15)

let rw1 = ((fst rf1),(snd rf1),[])
let rw2 = ((fst rf2),(snd rf2),[])
let rw0 = ((fst rf0),(snd rf0),[(RWA_Real rw1);(RWA_Real rw2)])

let if0 = (("Root1","IF"), 1)

let sim0 = (("Root1","Sim"), 1)
let sim2 = (("Root3","Sim"), 15)
let sim1 = (("Root2","Sim"), 10)

let iw =
{
  iw_ideal_func = if0;
  iw_main_sim = sim0;
  iw_other_sims = [sim2;sim1]
}

let w =
{
  worlds_real = rw0;
  worlds_ideal = iw;
}


let () =
  pp_worlds Format.std_formatter w 
