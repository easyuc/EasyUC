(* Forwarding *)

ec_requires KeysExponentsAndPlaintexts.

direct FwDir_ {
  in pt1@fw_req(pt2 : port, u : univ)
  out fw_rsp(pt1 : port, u : univ)@pt2
}

direct FwDir {D : FwDir_}

adversarial FwAdv {
  in  fw_ok
  out fw_obs(pt1 : port, pt2 : port, u : univ)
}

functionality Forw implements FwDir FwAdv {
  initial state Init {
    match message with
    | pt1@FwDir.D.fw_req(pt2, u) => {
        (* check that pt2 doesn't point into forwarder or adversary *)
        if (envport pt2) {
          send FwAdv.fw_obs(pt1, pt2, u) and transition Wait(pt1, pt2, u).
        }
        else { fail. }
      }
    | *                          => { fail. }
    end
  }

  state Wait(pt1 : port, pt2 : port, u : univ) {
    match message with
    | FwAdv.fw_ok => { send FwDir.D.fw_rsp(pt1, u)@pt2 and transition Final. }
    | *           => { fail. }
    end
  } 

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
