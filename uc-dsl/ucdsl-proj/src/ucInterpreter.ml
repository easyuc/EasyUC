(* UcInterpreter module *)

open EcSymbols
open EcTypes
open UcTypedSpec

(* the (positive) ints in a real_world, are the base adverserial port
   indices for the unit of the given functionality; these will also be
   the adversarial port indices for communication between the unit's
   ideal functionality and simulator *)

type real_world =
  | RWReal  of symb_pair * int * real_world list
  | RWIdeal of symb_pair * int

(* the (positive) ints in an ideal_world are the port indices for
   communication between ideal functionalities and simulators *)

type ideal_world = {
  iw_ideal_func : symb_pair * int;
  iw_main_sim   : symb_pair * int;
  iw_other_sims : (symb_pair * int) list
}

type worlds = {
  worlds_real  : real_world;
  worlds_ideal : ideal_world
}

