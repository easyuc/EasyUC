(* Forwarding.uc *)

(* Singleton unit consisting of a forwarding ideal functionality
   supporting multiple subss *)

ec_requires +SmtMap +Forwarding.

(* direct interface *)

direct FwDir' {
  (* pt1 starts new forwarding session subs to forward u to pt2 *)
  in pt1@req(subs : subs, pt2 : port, u : univ)

  (* pt1 asks whether session subs with pt2 is corrupted *)
  in pt1@is_corrupted_req(subs : subs, pt2 : port)

  (* message to pt2 giving it value u and saying it was forwarded
     from pt1 *)
  out rsp(subs : subs, pt1 : port, u : univ)@pt2

  (* response to pt1 communicating corruption status of session
     sub with pt2 *)
  out is_corrupted_rsp(subs : subs, pt2 : port, b : bool)@pt1
}

direct FwDir {D : FwDir'}

(* adversarial interface *)

adversarial FwAdv {
  (* observation message telling adversary that pt1 has
     started a forwarding session subs with pt2 asking to
     forward value u *)
  out obs(subs : subs, pt1 : port, pt2 : port, u : univ)

  (* message from adversary approving the forwarding of
     session subs between pt1 and pt2 *)
  in ok(subs : subs, pt1 : port, pt2 : port)

  (* message from adversary saying that the forwarding session subs
     between pt1 and pt2 should be corrupted, and instead value u_new
     should be sent to pt_new *)
  in corrupt(subs : subs, pt1 : port, pt2 : port, pt2' : port, u' : univ)
}

functionality Forw implements FwDir FwAdv {
  initial state Init {
    match message with
    | pt1@FwDir.D.req(subs, pt2, u) => {
        if (envport pt2) {
          send
            FwAdv.obs(subs, pt1, pt2, u)
          and transition
            Main(empty.[(subs, pt1, pt2) <- Wait u]).
        }
        else { fail. }
      }
    | *                             => { fail. }
    end
  }

  state Main(subs_map : (session, fwd_state) fmap) {
    match message with
    | pt1@FwDir.D.req(subs, pt2, u) => {
        if (envport pt2 /\ ! dom subs_map (subs, pt1, pt2)) {
          send
            FwAdv.obs(subs, pt1, pt2, u)
          and transition
            Main(subs_map.[(subs, pt1, pt2) <- Wait u]).
        }
        else { fail. }
      }
    | pt1@FwDir.D.is_corrupted_req(subs, pt2) => {
        if (dom subs_map (subs, pt1, pt2)) {
          match oget subs_map.[(subs, pt1, pt2)] with
          | Wait _    => {
              send
                FwDir.D.is_corrupted_rsp(subs, pt2, false)@pt1
              and transition
                Main(subs_map).
            }
          | Final cor => {
              send
                FwDir.D.is_corrupted_rsp(subs, pt2, cor)@pt1
              and transition
                Main(subs_map).
            }
          end
        }
        else { fail. }
      }
    | FwAdv.ok(subs, pt1, pt2) => {
        if (dom subs_map (subs, pt1, pt2)) {
          match oget subs_map.[(subs, pt1, pt2)] with
          | Wait u  => {
              send
                FwDir.D.rsp(subs, pt1, u)@pt2
              and transition
                Main(subs_map.[(subs, pt1, pt2) <- Final false]).
            }
          | Final _ => { fail. }
          end
        }
        else { fail. }
      }
    | FwAdv.corrupt(subs, pt1, pt2, pt2', u') => {
        if (dom subs_map (subs, pt1, pt2)) {
          match oget subs_map.[(subs, pt1, pt2)] with
          | Wait _  => {
              send
                FwDir.D.rsp(subs, pt1, u')@pt2'
              and transition
                Main(subs_map.[(subs, pt1, pt2) <- Final true]).
            }
          | Final _ => { fail. }
          end
        }
        else { fail. }
      }
    end
  } 
}
