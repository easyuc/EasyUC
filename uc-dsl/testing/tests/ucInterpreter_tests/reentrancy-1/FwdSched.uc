(* singleton unit, implementating the fowarding of universe values in
   which the adversary just plays the role of scheduler, learning
   nothing about the values begin forwarded or the ports involved *)

direct FwdSchedDir' {
  (* pt1 requesting to send u to pt2 *)

  in  pt1@req(pt2 : port, u : univ)

  (* response to pt2, containing u and the information that it
     came from pt1 *)

  out rsp(pt1 : port, u : univ)@pt2
}

(* we use a single party, as this is communication infrastructure
   that won't be realized *)

direct FwdSchedDir {D : FwdSchedDir'}

adversarial FwdSchedAdv {
  (* request approval to forward a value, giving the adversary
     no information about the value or the ports involved *)

  out req

  (* approve the forwarding *)

  in ok
}

functionality FwdSched implements FwdSchedDir FwdSchedAdv {
  initial state Init {
    match message with
    | pt1@FwdSchedDir.D.req(pt2, u) => {
        if (envport pt2) {
          send FwdSchedAdv.req
          and transition Wait(pt1, pt2, u).
        }
        else { fail. }
      }
    end
  }

  state Wait(pt1 : port, pt2 : port, u : univ) {
    match message with
    | FwdSchedAdv.ok => {
        send FwdSchedDir.D.rsp(pt1, u)@pt2
        and transition Final.
      }
    | *              => { fail. }
    end
  } 

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
