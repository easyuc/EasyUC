(* Commitment.uc *)

(* This contains a two party UC F_com ideal functionality, as described in Figure 2 of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf). This is a unit only containing one ideal functionality, no real functionalities (i.e. real protocol descriptions) and no simulators, and no extraneous interfaces *)

(* Import required .uc files *)
uc_requires Forwarding.

(* Import required easycrypt files. *)
ec_requires Cfptp Pke_indcpa.

(* Direct interfaces, which are between ideal functionality and environment, from ideal functionality's perspective. Note that the ideal functionality emulates parties. *)
direct CommDirPt1 {  (* Party 1, i.e. the Committer *)
  in pt1@commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment of a value u to pt2 *)

  in pt1@open_req()  (* message to pt2, asking to send the opening of the commitment to pt2 *)

  (* Corruption status messages *)
  in pt1@corrupted (* pt1 asks whether this party is corrupted *)

  out is_corrupted( is_corrupted : bool )@pt1 (* tells pt1 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)
}

direct CommDirPt2 {  (* Party 2, i.e. the Receiver *)
  out commit_rsp(pt1 : port)@pt2  (* message to pt2, saying that pt1 has committed a message u *)

  out open_rsp(u : bool)@pt2  (* message to pt2, saying that pt1 sent u to it *)

  (* Corruption status messages *)
  in pt2@corrupted (* pt2 asks whether this party is corrupted *)

  out is_corrupted( is_corrupted : bool )@pt2 (* tells pt2 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)
}

direct CommDir {
  Pt1 : CommDirPt1  (* Party 1 *)
  Pt2 : CommDirPt2  (* Party 2 *)

}

(* adversarial interface between ideal functionality and
   simulator, viewed from ideal functionality *)
adversarial CommI2S {

  (* Commit Phase *)
  out commit_req(pt1 : port, pt2 : port) (* Send both parties' port addresses to the simulator, where pt1 is the committer and pt2 is the receiver. *)

  in sim_party_corruptions(pt1_corrupted : bool, pt2_corrupted : bool) (* Receive from simulator whether each port pt is corrupted. True = corrupted. False = honest. *)

  out pt1_corrupted_input(u : bool option) (* If pt1 is corrupted, send its boolean input u to the simulator. Otherwise, send None. Note that pt2 has no input. *)

  in sim_commit_rsp(u' : bool option) (* Simulator OKs sending a commit message to pt2, conveying no additional information. It also has the option of detecting u' and returning it. *)

  (* Open Phase *)
  out open_req (* open message request from ideal functionality to simulator, conveying no additional information *)

  in sim_open_rsp (* simulator OKs sending a open message to pt2, conveying no additional information. Otherwise, send None. *)

}

(* ---- CRS ---- *)

(* Direct interface between CRS's ideal functionality and the environment *)
direct CRSDirPt {
  in pt@crs_req  (* request from pt, for the CRS *)

  out crs_rsp( crs : Cfptp.fkey * Pke_indcpa.pkey )@pt (* CRS is the forward key of claw-free pair of trapdoor permutations and the public key of the PKE scheme *)
}

direct CRSDir {
  Pt : CRSDirPt
}

(* basic adversarial interface between ideal functionality and simulator *)
adversarial CRS2Sim {
  out crs_req(pt : port, crs : Cfptp.fkey * Pke_indcpa.pkey ) (* Request to send the CRS string to party at pt *)

  in crs_rsp (* Simulator OKs and returns control to the CRS ideal functionality*)
}

functionality CRSIdeal implements CRSDir CRS2Sim {
  initial state WaitCRSInitReq {
    var fkey : Cfptp.fkey; var bkey : Cfptp.bkey;
    var pkey : Pke_indcpa.pkey; var skey : Pke_indcpa.skey;
    var crs : Cfptp.fkey * Pke_indcpa.pkey;
    match message with
    | pt@CRSDir.Pt.crs_req => {
        (* Sample values associated with CRS *)
 	(fkey, bkey) <$ Cfptp.keygen;
	(pkey, skey) <$ Pke_indcpa.dkeygen;
	crs <- (fkey, pkey);
        send CRS2Sim.crs_req(pt, crs)
	and transition WaitCRSRsp(pt, crs).
      }
    | *                => { fail. }
    end
  }

  state WaitCRSRsp(pt: port, crs : Cfptp.fkey * Pke_indcpa.pkey) {
    match message with
    | CRS2Sim.crs_rsp => {
        send CRSDir.Pt.crs_rsp(crs)@pt
	and transition WaitCRSReq(crs). (* Forget port pt after sending it the CRS *)
      }
    | *                => { fail. }
    end
  }

  state WaitCRSReq(crs : Cfptp.fkey * Pke_indcpa.pkey) {
    match message with
    | pt@CRSDir.Pt.crs_req => {
        send CRS2Sim.crs_req(pt, crs)
	and transition WaitCRSRsp(pt, crs).
      }
    | *                => { fail. }
    end
  }
}
(* ---- ---- *)

(* Ideal Functionality *)
functionality CommIdeal implements CommDir CommI2S {

  (* *)
  (* States for the static corruption interface *)
  (* *)
  initial state WaitCommitReq {
    match message with
    (* Pt1 (committer) requests to send a commit message to pt2 (receiver) *)
    | pt1@CommDir.Pt1.commit_req(pt2, b) => {
        send CommI2S.commit_req(pt1, pt2) (* Send the committer pt1 and pt2's port address to the simulator *)
        and transition WaitCorruptions(b, pt1, pt2). (* Transition to waiting for simulator's decision to corrupt pt1 *)
      }
    | *                => { fail. }
    end
  }

  state WaitCorruptions(b : bool, pt1 : port, pt2 : port) {
    match message with
    (* Simulator responds to ideal functionality saying whether pt1 is corrupted *)
    | CommI2S.sim_party_corruptions(pt1_corrupted, pt2_corrupted) => {
        send CommI2S.pt1_corrupted_input( pt1_corrupted ? (Some b) : (None) ) (* If pt1 is corrupted, send its input to the simulator. Otherwise send None. *)
        and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted). (* Transition to whether Sim OKs pt1's commit request *)
      }
    | *                => { fail. }
    end
  }

  (* *)
  (* States pertaining to commitment protocol *)
  (* *)

  state WaitCommitRsp(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool) {
    match message with
    (* Simulator oks delivery of pt1's commitment message to pt2. *)
    | CommI2S.sim_commit_rsp(b') => { (* b' is None if committer is not corrupted *)
        send CommDir.Pt2.commit_rsp(pt1)@pt2  (* Deliver pt1's commitment message to pt2, which excludes the commited value u *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, pt2_corrupted, b').   (* Transition to waiting for pt1's open message *)
      }
    | pt1@CommDir.Pt1.corrupted => { (* pt1 asks if it is corrupted *)
        send CommDir.Pt1.is_corrupted( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted). (* return to this same state *)
      }
    | pt2@CommDir.Pt2.corrupted => { (* pt2 asks if it is corrupted *)
        send CommDir.Pt2.is_corrupted( pt2_corrupted )@pt2 (* send pt2's corruption status *)
	and transition WaitCommitRsp(b, pt2, pt2, pt2_corrupted, pt2_corrupted). (* return to this same state *)
      }
    | *                => { fail. }
    end
  }

  state WaitOpenReq(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool, b' : bool option) {
    match message with
    (* Pt1 attempts to send an open message to pt2. Message is adversarially delayed, i.e. forwarded to Sim, who oks delivery. *)
    | pt1'@CommDir.Pt1.open_req => {
        if (pt1' = pt1) {
          send CommI2S.open_req  (* Ask simulator whether to deliver pt1's open message to pt2 *)
     	  and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted, b'). (* Transition to waiting for simulator's response *)
        }
        else {
          fail.
        }
      }
    | pt1@CommDir.Pt1.corrupted => { (* pt1 asks if it is corrupted *)
        send CommDir.Pt1.is_corrupted( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, pt2_corrupted, b'). (* return to this same state *)
      }
    | pt2@CommDir.Pt2.corrupted => { (* pt2 asks if it is corrupted *)
        send CommDir.Pt2.is_corrupted( pt2_corrupted )@pt2 (* send pt2's corruption status *)
	and transition WaitOpenReq(b, pt2, pt2, pt2_corrupted, pt2_corrupted, b'). (* return to this same state *)
      }
    | *                => { fail. }
    end
  }

  state WaitOpenRsp(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool, b' : bool option) {
    match message with
    (* Simulator oks delivery of pt1's open message, which includes b, to pt2. *)
    | CommI2S.sim_open_rsp => {
        match b' with
          | Some b' => {
	      send CommDir.Pt2.open_rsp(b')@pt2
	      and transition Final.
	    }
	  | None => {
	      send CommDir.Pt2.open_rsp(b)@pt2
	      and transition Final.
	    }
	  end
      }
    | pt1@CommDir.Pt1.corrupted => { (* pt1 asks if it is corrupted *)
        send CommDir.Pt1.is_corrupted( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted, b'). (* return to this same state *)
      }
    | pt2@CommDir.Pt2.corrupted => { (* pt2 asks if it is corrupted *)
        send CommDir.Pt2.is_corrupted( pt2_corrupted )@pt2 (* send pt2's corruption status *)
	and transition WaitOpenRsp(b, pt2, pt2, pt2_corrupted, pt2_corrupted, b'). (* return to this same state *)
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
