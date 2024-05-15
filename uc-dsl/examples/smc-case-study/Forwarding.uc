(* Forwarding *)

(* Singleton unit consisting of a forwarding ideal functionality. The
   adversary is allowed to delay but not alter message forwarding. *)

(* The basic direct interface for the single functionality party (because
   we won't have a real functionality, there is no reason not to use a
   single functionality party, to which forwarding requests come and from
   which forwarding responses originate).

   the identifiers in "pt1@" and "@pt2" as well as the parameter names
   can be usefully mentioned in documentation but are also used in the
   generation of EasyCrypt code. see below how they are used in
   message pattern matching and send and transition instructions. *)

direct FwDir' {
  in  pt1@fw_req(pt2 : port, u : univ)  (* message from pt1, requesting to send
    u to pt2 *)

  out fw_rsp(pt1 : port, u : univ)@pt2  (* message to pt2, saying that pt1
    sent u to it *)
}

(* The composite direct interface has a single component, corresponding to
   the single functionality party. *)

direct FwDir {D : FwDir'}

(* An ideal functionality must have a basic adversarial interface: *)

adversarial FwAdv {
  out fw_obs(pt1 : port, pt2 : port, u : univ)  (* inform adversary that
    pt1 wants to send u to pt2 *)

  in  fw_ok  (* adversary telling ideal functionality it can go ahead
    and send the universe value to its recipient *)
}

(* We say what direct (first) and adversarial (second) interfaces the
   functionality implements. This limits the possible messages
   coming/going from/to the environment and adversary. *)

functionality Forw implements FwDir FwAdv {
  initial state Init {  (* the functionality starts in this state *)
    match message with
    | pt1@FwDir.D.fw_req(pt2, u) => {
        (* pt1 gets bound to the source port of the incoming message
           (which will be guaranteed to be an envport, i.e., not to
           point into the forwarder or adversary), and pt2 and u will
           get bound to the data of the fw_req message

           we need to explicitly check that pt2 doesn't point into
           forwarder or adversary *)
        if (envport pt2) {
        (* a send-and-transition instruction sends a message (in this
           case a fw_obs message to the adversary) and notes that if
           control every returns to the functionality, that it should
           continue from the specified state with the given arguments
           (in this case Wait with data (pt1, pt2, u))

           a send-and-transition must never transition back to
           the initial state (this is true for real and ideal
           functionalities, and simulators)

           a send-and-transition of the initial state of an
           ideal functionality must always be an adversarial message,
           even when there is no simulator *)
          send FwAdv.fw_obs(pt1, pt2, u)     (* no destination port, *)
          and transition Wait(pt1, pt2, u).  (* as going to adversary *)
        }
        else { fail. }  (* failure gives control back to root of environment,
                           without changing the current state *)
      }
    (* adversarial messages can't be matched for in initial states,
       but automatically result in failure *)
    end
  }

  (* in the Wait state, we wait for the adversary to OK the forwarding *)

  state Wait(pt1 : port, pt2 : port, u : univ) {
    match message with
    | FwAdv.fw_ok => {  (* no source port bound, because from adversary *)
        (* in a send-and-transition where the message to be sent
           is a direct one, a check is implicitly made that the
           destination port is an envport; otherwise, the state
           is not changed and failure results

           (in this case, we know from the check in Init that pt2
           is an envport) *)
        send FwDir.D.fw_rsp(pt1, u)@pt2
        and transition Final.
      }
    | *           => { fail. }
    end
  } 

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
