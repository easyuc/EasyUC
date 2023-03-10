(* Key Exchange *)

(* Triple unit consisting of real and ideal functionalities, and a
   simulator, for Diffie-Hellman key exchange. *)

(* Requiring a .uc file makes the definitions of that file, plus those
   of all the EasyCrypt theories and .uc files required (directly, or
   indirectly) by that file available *with* explicit
   qualification. *)

uc_requires Forwarding.

(* Requiring an EasyCrypt theory makes the definitions of that theory,
   plus those of all the EasyCrypt theories required (directly or
   indirectly) by that theory, available: *with* qualification, if
   without a "+"; *without* qualification, if with a "+". *)

ec_requires +KeysExponentsAndPlaintexts.

(* The composite direct interface has two components, one for each
   of two parties. *)

direct KEDirPt1 {  (* Party 1 *)
  in  pt1@ke_req1(pt2 : port)  (* request from pt1, initiating the first
    round of key-exchange, asking to agree a key with pt2 *)

  out ke_rsp2(k : key)@pt1  (* response to pt1, ending the second round
    of key-exchange *)
}

direct KEDirPt2 {  (* Party 2 *)
  in  pt2@ke_req2  (* request from pt2, initiating the second round of
    key-exchange *)

  out ke_rsp1(pt1 : port, k : key)@pt2  (* response to pt2, ending the
    first round of key-exchange *)
}

direct KEDir {
  Pt1 : KEDirPt1  (* Party 1 *)
  Pt2 : KEDirPt2  (* Party 2 *)
}

(* The real functionality implements the composite direct interface
   KEDir. It could implement a composite adversarial interface, but
   does not in this case. *)

functionality KEReal implements KEDir {  (* no adversarial interface *)
  (* subfunctionalities - two forwarding functionalities
     subfunctionalities must be ideal functionalities *)

  subfun Fw1 = Forwarding.Forw  (* must be qualified *)
  subfun Fw2 = Forwarding.Forw

  (* Party 1 (Pt1) serves the basic direct interface KEDir.Pt1; this
     restricts the messages it can receive/send from/to the
     environment. It can also receive/send messages from/to the
     subfunctionalities Fw1 and Fw2. *)

  party Pt1 serves KEDir.Pt1 {
    initial state WaitReq1 {  (* Pt1 will start in this state *)
      var q1 : exp;  (* local non-persistent variable, just for this state *)
      match message with
      | pt1@KEDir.Pt1.ke_req1(pt2) => {
          if (envport pt2) {
            q1 <$ dexp;  (* sample q1 from distribution dexp *)
            (* send message to forwarder Fw1, asking to send the
               encoding of the triple (pt1, pt2, g ^ q1) to the
               internal port of Pt2 (Party 2); and transition to state
               WaitFwd2(pt1, pt2, q1), meaning that when control comes
               back to Pt1, it'll continue from this state *)
            send Fw1.D.fw_req
                 (intport Pt2,  (* internal port of Pt2 *)
                  epdp_port_port_key_univ.`enc (pt1, pt2, g ^ q1))
            and transition WaitFwd2(pt1, q1).
          }
          else { fail. }
        }
      | *                          => { fail. }
      end
    }

    state WaitFwd2(pt1 : port, q1 : exp) {
      match message with
      (* We can only respond to a response message from forwarder Fw2,
         which arrives on the internal port of Pt1, giving us the
         value u : univ that came from Pt2. The _ matches the port
         that made the forwarding request, which will be the internal
         port of Pt2.

         If a subfunctionality sends a message whose destination port
         isn't the internal port of one of the real functionality's
         parties, this is an error which results in a "fail", with
         control going back to the root of the environment (and
         the state not changing). (This also applies to messages from
         parameters of the real functionality - of which there are none
         in this case.) *)
      | Fw2.D.fw_rsp(_, u) => {
          (* we must decode u into a key, k2: *)
          match epdp_key_univ.`dec u with
          | Some k2 => {
              (* now Pt1 can send the agreed-upon key to pt1, and
                 transition to its final state *)
              send KEDir.Pt1.ke_rsp2(k2 ^ q1)@pt1 and transition Final.
            }
          | None    => { fail. }  (* will never happen *)
          end
        }
      | *                  => { fail. }
      end
    }
  
    state Final {
      match message with
      | * => { fail. }
      end
    }
  }

  (* Party 2 (Pt2) serves the basic direct interface KEDir.Pt2; this
     restricts the messages it can receive/send from/to the
     environment. It can also receive/send messages from/to the
     subfunctionalities Fw1 and Fw2. *)

  party Pt2 serves KEDir.Pt2 {
    initial state WaitFwd1 {
      var q2 : exp; var pt1, pt2 : port; var k1 : key;
      match message with
      | Fw1.D.fw_rsp(_, u) => {
          match epdp_port_port_key_univ.`dec u with
          | Some tr => {
              (pt1, pt2, k1) <- tr;
              q2 <$ dexp;
              send KEDir.Pt2.ke_rsp1(pt1, k1 ^ q2)@pt2
              and transition WaitReq2(pt2, q2).
            }
          | None    => { fail. }  (* cannot happen *)
          end
        }
      | *                  => { fail. }
      end
    }

    state WaitReq2(pt2 : port, q2 : exp) {
      match message with
      | pt2'@KEDir.Pt2.ke_req2 => { 
          if (pt2' = pt2) {
            send Fw2.D.fw_req(intport Pt1, epdp_key_univ.`enc (g ^ q2))
            and transition Final.
          }
          else { fail. }
        }
      | *                      => { fail. }
      end
    }

    state Final {
      match message with
      | * => { fail. }
      end
    }
  }
}

(* basic adversarial interface between ideal functionality and
   simulator *)

adversarial KEI2S {
  out ke_sim_req1(pt1 : port, pt2 : port)  (* message from ideal functionality
    to simulator, initiating the first round of simulation, and
    telling it the two ports involved in the key-exchange; this
    message implicitly tells the simulator the address of the ideal
    and thus real functionality *)

  in  ke_sim_rsp  (* response from simulator to ideal functionality,
    conveying no additional information; the is used to end the
    first and second rounds of simulation *)

  out ke_sim_req2  (* message from ideal functionality to simulator
    initiating the second round of simulation *)
}

(* The ideal functionality must implement the same composite direct
   interface as the real functionality. And it implements the basic
   adversarial interface it shares with the simulator. *)

functionality KEIdeal implements KEDir KEI2S {
  initial state WaitReq1 {
    match message with
    | pt1@KEDir.Pt1.ke_req1(pt2) => {
        if (envport pt2) {
          (* a send-and-transition of the initial state of an ideal
             functionality with a simulator must be to the simulator,
             implicitly letting the simulator know the address of
             the ideal and thus real functionality

             thus when an ideal functionality with a simulator is
             in a non-initial state, it knows its simulator has
             been woken up and can catch messages from the adversary
             destined for the real functionality *)
          send KEI2S.ke_sim_req1(pt1, pt2) and transition WaitSim1(pt1, pt2).
        }
        else { fail. }
      }
    | *                          => { fail. }
    end
  }

  state WaitSim1(pt1 : port, pt2 : port) {
    var q : exp;
    match message with
    | KEI2S.ke_sim_rsp => {
        q <$ dexp;
        send KEDir.Pt2.ke_rsp1(pt1, g ^ q)@pt2
        and transition WaitReq2(pt1, pt2, q).
      }
    | *                => { fail. }
    end
  }

  state WaitReq2(pt1 : port, pt2 : port, q : exp) {
    match message with
    | pt2'@KEDir.Pt2.ke_req2 => {
        if (pt2' = pt2) {
          send KEI2S.ke_sim_req2 and transition WaitSim2(pt1, pt2, q).
        }
        else { fail. }
      }
    | *                      => { fail. }
    end
  }

  state WaitSim2(pt1 : port, pt2 : port, q : exp) {
    match message with
    | KEI2S.ke_sim_rsp => {
        send KEDir.Pt1.ke_rsp2(g ^ q)@pt1 and transition Final.
      }
    | *                => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}

(* The simulator "uses" the basic adversarial interface shared with
   the ideal functionality, and it "simulates" the real functionality.
   From the point of view of the simulator, the directions (in/out) of
   the messages of KEI2S are inverted.

   Messages between the environment and adversary automatically flow
   through the simulator, which has no option to interfere with them.

   When simulating the real functionality, the simulator needs to
   send messages to the simulator and receive messages from the
   simulator as if it were the real functionality. In its initial state,
   though, it doesn't know the address of the real functionality, and
   thus any messages from the adversary to the real functionality
   (or its subfunctionalities (or parameters, which don't exists in
   this case)) will flow through the simulator and go to the ideal
   functionality, which must be written to expect them. *)

simulator KESim uses KEI2S simulates KEReal {
  initial state WaitReq1 {
    var q1 : exp;
    match message with 
    | KEI2S.ke_sim_req1(pt1, pt2) => {
        (* simulator implicitly learns address of ideal functionality,
           which is the same as that of the real functionality *)
        q1 <$ dexp;
        (* pretend to be the first forwarder of the real functionality,
           sending its obversation message to the adversary, saying
           the internal port of Pt1 is trying to communicate to
           the internal port of Pt2 the encoding of the triple
           (pt1, pt2, g ^ q1) *)
        send KEReal.Fw1.FwAdv.fw_obs
             (intport KEReal.Pt1, intport KEReal.Pt2,
              epdp_port_port_key_univ.`enc (pt1, pt2, g ^ q1))
        and transition WaitAdv1(q1).
      }    
    | *                           => { fail. }
    (* only catches KEI2S.ke_sim_req2; messages from adversary to real
       functionality flow through the simulator to the ideal
       functionality, where they result in failure *)
    end
  }

  state WaitAdv1(q1 : exp) {
    var q2 : exp;
    match message with 
    (* because this isn't the initial state, we can pattern match
       for messages intended for the real functionality, like this
       OK message destined for the first forwarder *)
    | KEReal.Fw1.FwAdv.fw_ok => {
        q2 <$ dexp;
        send KEI2S.ke_sim_rsp and transition WaitReq2(q1, q2).
      }
    (* messages with addresses not >= address of ideal functionality
       are implicitly passed to environment *)
    | * => { fail. }
    end
  }

  state WaitReq2(q1 : exp, q2 : exp) {
    match message with 
    | KEI2S.ke_sim_req2 => {
        send KEReal.Fw2.FwAdv.fw_obs
             (intport KEReal.Pt2, intport KEReal.Pt1,
              epdp_key_univ.`enc (g ^ q2))
        and transition WaitAdv2(q1, q2).
      }
    | *                 => { fail. }
    end
  }

  state WaitAdv2(q1 : exp, q2 : exp) {
    match message with 
    | KEReal.Fw2.FwAdv.fw_ok => {
        send KEI2S.ke_sim_rsp and transition Final.
      }
    | *                      => { fail. }
    end
   }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
