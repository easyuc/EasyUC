(* Crs.uc *)

(* This contains the ideal functionality of a multisession common reference string (CRS) functionality used for the protocol in Commitment.uc. *)

(* Author: Megan Chen *)

(* Import required easycrypt files. *)
ec_requires Cfptp Pke ForwardingEncodings.


(* Direct interface between CRS's ideal functionality and the environment *)
direct DirPt {
  in pt@crs_req  (* request from pt, for the CRS *)

  out crs_rsp( crs : Cfptp.fkey * Pke.pkey )@pt (* CRS is the forward key of claw-free pair of trapdoor permutations and the public key of the PKE scheme *)
}

direct Dir {
  Pt : DirPt
}

(* basic adversarial interface between ideal functionality and simulator *)
adversarial Adv {
  out crs_send_req(pt : port, crs : Cfptp.fkey * Pke.pkey ) (* Request to send the CRS string to party at pt *)

  in crs_send_ok (* Simulator OKs and returns control to the CRS ideal functionality*)
}

(* TODO:
Make multiple session version of CRS.
Sample CRS. Use multisessions to take care of talking to different ports.
Look at multisession forwarder in sessions directory.
Initial state - respond to either the env or adv. multisession occurs after.
*)
functionality Ideal implements Dir Adv {
  initial state WaitInitReq {
    var fk : Cfptp.fkey; var bk : Cfptp.bkey;
    var pk : Pke.pkey; var sk : Pke.skey;
    var crs : Cfptp.fkey * Pke.pkey;
    match message with
    | pt@Dir.Pt.crs_req => {
        (* Sample values associated with CRS *)
 	(fk, bk) <$ Cfptp.keygen;
	(pk, sk) <$ Pke.dkeygen;
	crs <- (fk, pk);
        send Adv.crs_send_req(pt, crs)
	and transition WaitRsp(pt, crs).
      }
    | * => { fail. }
    end
  }

  state WaitRsp(pt: port, crs : Cfptp.fkey * Pke.pkey) {
    match message with
    | Adv.crs_send_ok => {
        send Dir.Pt.crs_rsp(crs)@pt
	and transition WaitReq(crs). (* Forget port pt after sending it the CRS *)
      }
    | * => { fail. }
    end
  }

  state WaitReq(crs : Cfptp.fkey * Pke.pkey) {
    match message with
    | pt@Dir.Pt.crs_req => {
        send Adv.crs_send_req(pt, crs)
	and transition WaitRsp(pt, crs).
      }
    | * => { fail. }
    end
  }
}
