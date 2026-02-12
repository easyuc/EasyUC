(* Secure Message Communication *)

(* Triple unit for two way secure message communcation between two
   parties, with two different types of plain texts *)

uc_requires (*Forwarding*) SMC.

ec_requires +EPDPAux.

(**************************** Begin Unit Parameters ***************************)

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)

op kid : key.  (* identity *)

op kinv : key -> key.  (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom kid_l (x : key) : kid ^^ x = x.

axiom kid_r (x : key) : x ^^ kid = x.

axiom kinv_l (x : key) : kinv x ^^ x = kid.

axiom kinv_r (x : key) : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op epdp_exp_univ : (exp, univ) epdp.  (* EPDP from exp to univ *)

axiom valid_epdp_exp_univ : valid_epdp epdp_exp_univ.

(* full (every element has non-zero weight), uniform (all elements
   with non-zero weight have same weight) and lossless (sum of all
   weights is 1%r) distribution over exp

   consequently exp has only finitely many elements *)

op [full uniform lossless] dexp : exp distr.

(* connection between key and exp, via generator key and
   exponentiation operation *)

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* the following axioms say that each key is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : key) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(* two types of plain texts, both with EPDPs to key *)

type text1.

op epdp_text1_key : (text1, key) epdp.  (* EPDP from text1 to key *)

axiom valid_epdp_text1_key : valid_epdp epdp_text1_key.

type text2.

op epdp_text2_key : (text2, key) epdp.  (* EPDP from text2 to key *)

axiom valid_epdp_text2_key : valid_epdp epdp_text2_key.

(***************************** End Unit Parameters ****************************)

uc_clone Forwarding as Forwarding1.
uc_clone Forwarding as Forwarding2.

uc_clone SMC as SMC2 with
  type key         = key,
  op (^^)          = (^^),
  op kid           = kid,
  op kinv          = kinv,
  type exp         = exp,
  op e             = e,
  op ( * )         = ( * ),
  op epdp_exp_univ = epdp_exp_univ,
  op dexp          = dexp,
  op g             = g,
  op (^)           = (^),
  type text        = text2,
  op epdp_text_key = epdp_text2_key.

uc_clone SMC as SMC1 with
  type key         = key,
  op (^^)          = (^^),
  op kid           = kid,
  op kinv          = kinv,
  type exp         = exp,
  op e             = e,
  op ( * )         = ( * ),
  op epdp_exp_univ = epdp_exp_univ,
  op dexp          = dexp,
  op g             = g,
  op (^)           = (^),
  type text        = text1,
  op epdp_text_key = epdp_text1_key.

direct SMC2Pt1 {
  in  pt1@smc_req(pt2 : port, t : text1)  (* 1 *)
  out smc_rsp(t : text2)@pt1              (* 4 *)
}

direct SMC2Pt2 {
  out smc_rsp(pt1 : port, t : text1)@pt2  (* 2 *)
  in  pt2@smc_req(t : text2)              (* 3 *)
}

direct SMC2Dir {
  Pt1 : SMC2Pt1
  Pt2 : SMC2Pt2
}

functionality SMC2Real(SMC1 : SMC1.SMCDir, SMC2 : SMC2.SMCDir)
    implements SMC2Dir {
  subfun Fwd1 = Forwarding1.Forw
  subfun Fwd2 = Forwarding2.Forw

  party Pt1 serves SMC2Dir.Pt1 {
    initial state WaitReq {
      match message with 
      | pt1@SMC2Dir.Pt1.smc_req(pt2, t) => {
          if (envport pt2 /\ SMC1.KeyExchange.Forwarding1.Forwarding.fwd_const = 3) {
            send Fwd1.D.fw_req
                 (intport Pt2, epdp_port_port_univ.`enc (pt1, pt2))
            and transition WaitFwd2(pt1, t).
          }
          else { fail. }
        }
      | *                               => { fail. }
      end
    }

    state WaitFwd2(pt1 : port, t : text1) {
      match message with
      | Fwd2.D.fw_rsp(_, _) => {
          send SMC1.Pt1.smc_req(intport Pt2, t)
          and transition WaitSMC2(pt1).
        }
      | *                   => { fail. }
      end         
    }

    state WaitSMC2(pt1 : port) {
      match message with 
      | SMC2.Pt2.smc_rsp(_, t) => {
          send SMC2Dir.Pt1.smc_rsp(t)@pt1
          and transition Final.
        }
      | *                       => { fail. }
      end
    }

    state Final {
      match message with 
      | * => { fail. }
      end
    }
  }

  party Pt2 serves SMC2Dir.Pt2 {
    initial state WaitFwd1 {
      var pt1, pt2 : port;
      match message with 
      | Fwd1.D.fw_rsp(_, u) => {
          (pt1, pt2) <- oget (epdp_port_port_univ.`dec u);
          send Fwd2.D.fw_req(intport Pt1, [])
          and transition WaitSMC1(pt1, pt2).
        }
      | *                   => { fail. }
      end
    }

    state WaitSMC1(pt1 : port, pt2 : port) {
      match message with
      | SMC1.Pt2.smc_rsp(_, t) => {
          send SMC2Dir.Pt2.smc_rsp(pt1, t)@pt2
          and transition WaitReq(pt2).
        }
      | *                      => { fail. }
      end
    }

    state WaitReq(pt2 : port) {
      match message with 
      | pt2'@SMC2Dir.Pt2.smc_req(t) => {
          if (pt2' = pt2) {
            send SMC2.Pt1.smc_req(intport Pt1, t)
            and transition Final.
          }
          else { fail. }
        }
      | *                           => { fail. }
      end
    }

    state Final {
      match message with 
      | * => { fail. }
      end
    }
  }
}

adversarial SMC2IF_to_Sim {
  out sim_req1(pt1 : port, pt2 : port)
  out sim_req2
  in  sim_rsp
}

functionality SMC2Ideal implements SMC2Dir SMC2IF_to_Sim {
  initial state WaitReq1 {
    match message with 
    | pt1@SMC2Dir.Pt1.smc_req(pt2, t) => {
        if (envport pt2) {
          send SMC2IF_to_Sim.sim_req1(pt1, pt2)
          and transition WaitSim1(pt1, pt2, t).
        }
        else { fail. }
      }
    | *                               => { fail. }
    end
  }

  state WaitSim1(pt1 : port, pt2 : port, t : text1) {
    match message with
    | SMC2IF_to_Sim.sim_rsp => {
        send SMC2Dir.Pt2.smc_rsp(pt1, t)@pt2
        and transition WaitReq2(pt1, pt2).
      }
    | *                     => { fail. }
    end
  }        

  state WaitReq2(pt1 : port, pt2 : port) {
    match message with 
    | pt2'@SMC2Dir.Pt2.smc_req(t) => {
        if (pt2' = pt2) {
          send SMC2IF_to_Sim.sim_req2
          and transition WaitSim2(pt1, t).
        }
        else { fail. }
      }
    | *                           => { fail. }
    end
  }

  state WaitSim2(pt1 : port, t : text2) {
    match message with
    | SMC2IF_to_Sim.sim_rsp => {
        send SMC2Dir.Pt1.smc_rsp(t)@pt1
        and transition Final.
      }
    | *                     => { fail. }
    end
  }        

  state Final {
    match message with
    | * => { fail. }
    end
  }
}

simulator SMC2Sim uses SMC2IF_to_Sim
          simulates SMC2Real(SMC1.SMCIdeal, SMC2.SMCIdeal) {
  initial state WaitReq1 {
    match message with 
    | SMC2IF_to_Sim.sim_req1(pt1, pt2) => {
        send SMC2Real.Fwd1.FwAdv.fw_obs
             (intport SMC2Real.Pt1, intport SMC2Real.Pt2,
              epdp_port_port_univ.`enc (pt1, pt2))
        and transition WaitAdv1.
      }
    | *                                => { fail. }
    end
  }

  state WaitAdv1 {
    match message with
    | SMC2Real.Fwd1.FwAdv.fw_ok => {
        send SMC2Real.Fwd2.FwAdv.fw_obs
             (intport SMC2Real.Pt2, intport SMC2Real.Pt1, [])
        and transition WaitAdv2.
      }
    | *                         => { fail. }        
    end
  }

  state WaitAdv2 {
    match message with
    | SMC2Real.Fwd2.FwAdv.fw_ok => {
        send SMC2Real.SMC1.SMC2Sim.sim_req
             (intport SMC2Real.Pt1, intport SMC2Real.Pt2)
        and transition WaitAdv3.
      }
    | *                         => { fail. }
    end
  }

  state WaitAdv3 {
    match message with
    | SMC2Real.SMC1.SMC2Sim.sim_rsp => {
        send SMC2IF_to_Sim.sim_rsp
        and transition WaitReq2.
      }
    | *                             => { fail. }
    end
  }

  state WaitReq2 {
    match message with 
    | SMC2IF_to_Sim.sim_req2 => {
        send SMC2Real.SMC2.SMC2Sim.sim_req
             (intport SMC2Real.Pt2, intport SMC2Real.Pt1)
        and transition WaitAdv4.
      }
    | *                      => { fail. }
    end
  }

  state WaitAdv4 {
    match message with
    | SMC2Real.SMC2.SMC2Sim.sim_rsp => {
        send SMC2IF_to_Sim.sim_rsp
        and transition Final.
      }
    | *                             => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
