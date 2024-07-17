(* Private Forwarding *)

direct FwDir' {
  in  pt1@fw_req(pt2 : port, u : univ)  (* message from pt1, requesting to send
    u to pt2 *)

  out fw_rsp(pt1 : port, u : univ)@pt2  (* message to pt2, saying that pt1
    sent u to it *)
}

direct FwDir {D : FwDir'}

(* No adversarial basic interface *)

functionality Forw implements FwDir {
  initial state Init {
    match message with
    | pt1@FwDir.D.fw_req(pt2, u) => {
        if (envport pt2) {
          send FwDir.D.fw_rsp(pt1, u)@pt2
          and transition Final.
        }
        else { fail. }
      }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
