(* Forwarding *)

(* Singleton unit consisting of a forwarding ideal functionality
   supporting multiple sessions *)

ec_requires +Forwarding.  (* defines needed types *)

(* direct interface *)

direct FwDir' {
  (* request by instance ins1 of port pt1, asking to send u to
     iport ipt2 *)

  in pt1@fw_req(ins1 : inst, ipt2 : iport, u : univ)

  (* response from functionality to instance ins2 of port pt2, saying
     iport ipt1 sent it u *)

  out fw_rsp(ipt1 : iport, ins2 : inst, u : univ)@pt2
}

direct FwDir {D : FwDir'}

(* adversarial interface *)

adversarial FwAdv {
  (* tell adversary that, in forwarding session ssn, iport ipt1
     is trying to forward u to iport ipt2 *)

  out fw_obs(ssn : int, ipt1 : iport, ipt2 : iport, u : univ)

  (* adversary approves the forwarding of session ssn *)

  in fw_ok(ssn : int)
}

functionality Forw implements FwDir FwAdv {
  initial state Init {
    match message with
    | pt1@FwDir.D.fw_req(ins1, ipt2, u) => {
        if (envport ipt2.`1) {
          send
            FwAdv.fw_obs(0, (pt1, ins1), ipt2, u)
          and transition
            Main(1, init.[0 <- ((pt1, ins1), ipt2, u)]).
        }
        else { fail. }
      }
    | *                                 => { fail. }
    end
  }

  state Main(next : int, ssns : sessions) {
    var ipt1', ipt2' : iport; var u' : univ;
    match message with
    | pt1@FwDir.D.fw_req(ins1, ipt2, u) => {
        if (envport ipt2.`1) {
          send
            FwAdv.fw_obs(next, (pt1, ins1), ipt2, u)
          and transition
            Main(next + 1, ssns.[next <- ((pt1, ins1), ipt2, u)]).
        }
        else { fail. }
      }
    | FwAdv.fw_ok(ssn) => {
        if (dom ssns ssn) {
          (ipt1', ipt2', u') <- oget ssns.[ssn];
          send
            FwDir.D.fw_rsp(ipt1', ipt2'.`2, u')@ipt2'.`1
          and transition
            Main(next, rem ssns ssn).
          }
        else { fail. }
      }
    end
  } 
}
