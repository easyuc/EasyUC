(* Forwarding *)

(* Singleton unit consisting of a forwarding ideal functionality
   supporting multiple sessions *)

ec_requires +Forwarding.  (* defines sessions map type *)

(* direct interface *)

direct FwDir' {
  in  pt1@fw_req(pt2 : port, u : univ)  (* pt1 starts a forwarding
        session, sending u to pt2 *)

  out fw_rsp(ssn : int, pt1 : port, u : univ)@pt2  (* end of forwarding
        session ssn, sending u to pt2, and saying this was session ssn
        and pt1 initiated the forwarding *)
}

direct FwDir {D : FwDir'}

(* adversarial interface *)

adversarial FwAdv {
  out fw_obs(ssn : int, pt1 : port, pt2 : port, u : univ)  (* tell adversary
        that session ssn consists of pt1 trying to send u to pt2 *)

  in fw_ok(ssn : int)  (* adversary approves the forwarding of session ssn *)
}

functionality Forw implements FwDir FwAdv {
  initial state Init {
    match message with
    | pt1@FwDir.D.fw_req(pt2, u) => {
        if (envport pt2) {
          send
            FwAdv.fw_obs(0, pt1, pt2, u)
          and transition
            Main(1, init.[0 <- (pt1, pt2, u)]).
        }
        else { fail. }
      }
    | *                          => { fail. }
    end
  }

  state Main(next : int, ssns : sessions) {
    var pt1', pt2' : port; var u' : univ;
    match message with
    | pt1@FwDir.D.fw_req(pt2, u) => {
        if (envport pt2) {
          send
            FwAdv.fw_obs(next, pt1, pt2, u)
          and transition
            Main(next + 1, ssns.[next <- (pt1, pt2, u)]).
        }
        else { fail. }
      }
    | FwAdv.fw_ok(ssn) => {
        if (dom ssns ssn) {
          (pt1', pt2', u') <- oget ssns.[ssn];
          send
            FwDir.D.fw_rsp(ssn, pt1', u')@pt2'
          and transition
            Main(next, rem ssns ssn).
        }
        else {
          fail.
        }
      }
    end
  } 
}

