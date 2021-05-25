(* Commitment.uc *)

(* This contains a two party UC F_com ideal functionality, as described in Figure 2 of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf). This is a unit only containing one ideal functionality, no real functionalities (i.e. real protocol descriptions) and no simulators, and no extraneous interfaces *)

(* Author: Megan Chen *)

(* Import required .uc files *)
uc_requires Forwarding.

(* Import required easycrypt files. *)
ec_requires Cfptp Pke_indcpa Encodings.

(* Direct interfaces, which are between ideal functionality and environment, from ideal functionality's perspective. Note that the ideal functionality emulates parties. *)
direct DirPt1 {  (* Party 1, i.e. the Committer *)
  in pt1@commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment of a value u to pt2 *)

  in pt1@open_req  (* message to pt2, asking to send the opening of the commitment to pt2 *)

  (* Corruption status messages *)
  in pt1@committer_corrupted_req (* pt1 asks whether Committer is corrupted *)

  out committer_corrupted_rsp( is_corrupted : bool )@pt1 (* tells pt1 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)
}

direct DirPt2 {  (* Party 2, i.e. the Verifier *)
  out commit_rsp(pt1 : port)@pt2  (* message to pt2, saying that pt1 has committed a message u *)

  out open_rsp(u : bool)@pt2  (* message to pt2, saying that pt1 sent u to it *)

  (*
  (* Corruption status messages *)
  in pt2@verifier_corrupted_req (* pt2 asks whether this party is corrupted *)

  out verifier_corrupted_rsp( is_corrupted : bool )@pt2 (* tells pt2 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)
  *)
}

direct Dir {
  Pt1 : DirPt1  (* Party 1 *)
  Pt2 : DirPt2  (* Party 2 *)

}

(* adversarial interface between ideal functionality and
   simulator, viewed from ideal functionality *)
adversarial I2S {

  (* Commit Phase *)
  out commit_req(pt1 : port, pt2 : port) (* Send both parties' port addresses to the simulator, where pt1 is the committer and pt2 is the verifier. *)

  in sim_committer_corruption(pt1_corrupted : bool(*, pt2_corrupted : bool*)) (* Receive from simulator whether each port pt is corrupted. True = corrupted. False = honest. *)

  out pt1_corrupted_input(u : bool option) (* If pt1 is corrupted, send its boolean input u to the simulator. Otherwise, send None. Note that pt2 has no input. *)

  in sim_commit_rsp(u' : bool option) (* Simulator OKs sending a commit message to pt2, conveying no additional information. It also has the option of detecting u' and returning it. *)

  (* Open Phase *)
  out open_req(b' : bool option) (* open message request from ideal functionality to simulator. If it knows the bit b' to be opened, return it. *)

  in sim_open_rsp (* simulator OKs sending a open message to pt2, conveying no additional information. Otherwise, send None. *)

}

(* ---- CRS ---- *)

(* Direct interface between CRS's ideal functionality and the environment *)
direct CrsDirPt {
  in pt@crs_req  (* request from pt, for the CRS *)

  out crs_rsp( crs : Cfptp.fkey * Pke_indcpa.pkey )@pt (* CRS is the forward key of claw-free pair of trapdoor permutations and the public key of the PKE scheme *)
}

direct CrsDir {
  Pt : CrsDirPt
}

(* basic adversarial interface between ideal functionality and simulator *)
adversarial CrsI2S {
  out crs_req(pt : port, crs : Cfptp.fkey * Pke_indcpa.pkey ) (* Request to send the CRS string to party at pt *)

  in crs_rsp (* Simulator OKs and returns control to the CRS ideal functionality*)
}

functionality CrsIdeal implements CrsDir CrsI2S {
  initial state WaitCrsInitReq {
    var fk : Cfptp.fkey; var bk : Cfptp.bkey;
    var pk : Pke_indcpa.pkey; var sk : Pke_indcpa.skey;
    var crs : Cfptp.fkey * Pke_indcpa.pkey;
    match message with
    | pt@CrsDir.Pt.crs_req => {
        (* Sample values associated with CRS *)
 	(fk, bk) <$ Cfptp.keygen;
	(pk, sk) <$ Pke_indcpa.dkeygen;
	crs <- (fk, pk);
        send CrsI2S.crs_req(pt, crs)
	and transition WaitCrsRsp(pt, crs).
      }
    | * => { fail. }
    end
  }

  state WaitCrsRsp(pt: port, crs : Cfptp.fkey * Pke_indcpa.pkey) {
    match message with
    | CrsI2S.crs_rsp => {
        send CrsDir.Pt.crs_rsp(crs)@pt
	and transition WaitCrsReq(crs). (* Forget port pt after sending it the CRS *)
      }
    | * => { fail. }
    end
  }

  state WaitCrsReq(crs : Cfptp.fkey * Pke_indcpa.pkey) {
    match message with
    | pt@CrsDir.Pt.crs_req => {
        send CrsI2S.crs_req(pt, crs)
	and transition WaitCrsRsp(pt, crs).
      }
    | * => { fail. }
    end
  }
}
(* ---- ---- *)

(* Ideal Functionality *)
functionality Ideal implements Dir I2S {

  (* *)
  (* States for the static corruption interface *)
  (* *)
  initial state WaitCommitReq {
    match message with
    (* Pt1 (committer) requests to send a commit message to pt2 (verifier) *)
    | pt1@Dir.Pt1.commit_req(pt2, b) => {
        send I2S.commit_req(pt1, pt2) (* Send the committer pt1 and pt2's port address to the simulator *)
        and transition WaitCorruptions(b, pt1, pt2). (* Transition to waiting for simulator's decision to corrupt pt1 *)
      }
    | * => { fail. }
    end
  }

  state WaitCorruptions(b : bool, pt1 : port, pt2 : port) {
    match message with
    (* Simulator responds to ideal functionality saying whether pt1 is corrupted *)
    | I2S.sim_committer_corruption(pt1_corrupted) => {
        send I2S.pt1_corrupted_input( pt1_corrupted ? (Some b) : (None) ) (* If pt1 is corrupted, send its input to the simulator. Otherwise send None. *)
        and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted). (* Transition to whether Sim OKs pt1's commit request *)
      }
    | * => { fail. }
    end
  }

  (* *)
  (* States pertaining to commitment protocol *)
  (* *)

  state WaitCommitRsp(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool) {
    match message with
    (* Simulator oks delivery of pt1's commitment message to pt2. *)
    | I2S.sim_commit_rsp(b') => { (* b' is None if committer is not corrupted *)
        send Dir.Pt2.commit_rsp(pt1)@pt2  (* Deliver pt1's commitment message to pt2, which excludes the commited value u *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, b').   (* Transition to waiting for pt1's open message *)
      }
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted). (* return to this same state *)
      }
    (* Can't query pt2 for verifier's corruption status until V client has been activated.
    | pt2@Dir.Pt2.verifier_corrupted_req => { (* pt2 asks if it is corrupted *)
        send Dir.Pt2.verifier_corrupted_rsp( pt2_corrupted )@pt2 (* send pt2's corruption status *)
	and transition WaitCommitRsp(b, pt2, pt2, pt2_corrupted, pt2_corrupted). (* return to this same state *)
      }
    *)
    | * => { fail. }
    end
  }

  state WaitOpenReq(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, b' : bool option) {
    match message with
    (* Pt1 attempts to send an open message to pt2. Message is adversarially delayed, i.e. forwarded to Sim, who oks delivery. *)
    | pt1'@Dir.Pt1.open_req => {
        if (pt1' = pt1) {
          send I2S.open_req(b')  (* Ask simulator whether to deliver pt1's open message to pt2 *)
     	  and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, b'). (* Transition to waiting for simulator's response *)
        }
        else {
          fail.
        }
      }
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, b'). (* return to this same state *)
      }
    (*
    | pt2@Dir.Pt2.verifier_corrupted_req => { (* pt2 asks if it is corrupted *)
        send Dir.Pt2.verifier_corrupted_rsp( pt2_corrupted )@pt2 (* send pt2's corruption status *)
	and transition WaitOpenReq(b, pt2, pt2, pt2_corrupted, pt2_corrupted, b'). (* return to this same state *)
      }
    *)
    | * => { fail. }
    end
  }

  state WaitOpenRsp(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, b' : bool option) {
    match message with
    (* Simulator oks delivery of pt1's open message, which includes b, to pt2. *)
    | I2S.sim_open_rsp => {
        match b' with
          | Some b' => {
	      send Dir.Pt2.open_rsp(b')@pt2
	      and transition Final.
	    }
	  | None => {
	      send Dir.Pt2.open_rsp(b)@pt2
	      and transition Final.
	    }
	  end
      }
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, b'). (* return to this same state *)
      }
    (*
    | pt2@Dir.Pt2.verifier_corrupted_req => { (* pt2 asks if it is corrupted *)
        send Dir.Pt2.verifier_corrupted_rsp( pt2_corrupted )@pt2 (* send pt2's corruption status *)
	and transition WaitOpenRsp(b, pt2, pt2, pt2_corrupted, pt2_corrupted, b'). (* return to this same state *)
      }
    *)
    | * => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}

(* Adversarial interfaces between a real party and the adversary, from the perspective of the real party *)
adversarial Pt1Adv {

  (* Corruption sequence *)
  out committer_corrupted (* Ask adversary if the committer is corrupted *)

  in committer_corruption_status( corrupted : bool ) (* corrupted = true if corrupted. corrupted = false if the party is honest *)

  out committer_corruption_data(opt : (port * port * bool) option) (* sends None if committer is not corrupted. Sends all known data if committer is corrupted.*)

  in continue (* Adv response message that returns control to committer *)

  (* Post-corruption messages with the adversary *)
  out adv_commit_msg_req(fk : Cfptp.fkey, pk : Pke_indcpa.pkey) (* Forward received information to the adversary *)

  in adv_commit_msg_rsp(y': Cfptp.D, c_b': Pke_indcpa.ciphertext, c_nb': Pke_indcpa.ciphertext) (* Adv responds with the y, c_b, c_bn values it wants to send to the verifier *)

  out adv_gen_open_msg (* Ask adv for the open message *)

  in adv_open_msg(b' : bool, x' : Cfptp.D, rb' : Pke_indcpa.rand)
}

adversarial Pt2Adv {

  (* Corruption sequence *)
  out verifier_corrupted_req (* Ask adversary if the verifier is corrupted *)

  in verifier_corrupted_rsp( corrupted : bool ) (* corrupted = true if corrupted. corrupted = false if the party is honest *)
}

(* Composite adversarial interface between parties and adversary *)
adversarial Adv {
  Pt1 : Pt1Adv (* Adversary that talks to Pt1 *)
  Pt2 : Pt2Adv (* Adversary that talks to Pt2 *)
}

(* Real Protocol *)
functionality Real implements Dir Adv{
  subfun Fwd1 = Forwarding.Forw (* For commit phase *)
  subfun Fwd2 = Forwarding.Forw (* For open phase *)
  subfun Crs = CrsIdeal

  party Committer serves Dir.Pt1 Adv.Pt1 {

    initial state WaitCommReq {
      match message with
      | pt1@Dir.Pt1.commit_req(pt2, b) => {
          (* get committer's corruption status *)
	  send Adv.Pt1.committer_corrupted
	  and transition WaitCorruptionStatus(pt1, pt2, b).
	}
      | * => { fail. }
      end
    }

    state WaitCorruptionStatus(pt1 : port, pt2 : port, b : bool) {
      match message with
      | Adv.Pt1.committer_corruption_status( corrupted ) => {
          send Adv.Pt1.committer_corruption_data( corrupted ? Some(pt1, pt2, b) : None)
	  and transition WaitContinue(pt1, pt2, b, corrupted).
	}
      | * => { fail. }
      end
    }

    state WaitContinue(pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      match message with
      | Adv.Pt1.continue => {
      	  if (corrupted) {
	    send Crs.Pt.crs_req
	    and transition WaitCrsCorrupted(pt1, pt2, b, corrupted). (* Go to states modelling corrupted committer *)
	  }
	  else {
            (* get CRS *)
	    send Crs.Pt.crs_req
	    and transition WaitCrs(pt1, pt2, b, corrupted). (* Go to states modelling honest committer *)
	  }
	}
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the committer is HONEST *)
    (* --- --- --- --- --- ---  *)
    state WaitCrs(pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      var x : Cfptp.D;
      var r0, r1 : Pke_indcpa.rand;
      var y : Cfptp.D;
      var c_b, c_nb : Pke_indcpa.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke_indcpa.pkey;

      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)

	  (* generate commit message *)
	  x <$ Pke_indcpa.dplaintext; (* Megan: how to reconcile that this also needs to be interpreted as type Cfptp.D? *)
	  r0 <$ Pke_indcpa.drand;
	  r1 <$ Pke_indcpa.drand;

	  y <- Cfptp.forw fk x b; (* compute f_b(x), where f_b is a cfptp. *)
	  c_b <- Pke_indcpa.enc pk x (b ? r1 : r0); (* ciphertext c_b. Encrypt x using r1 if b = true, r0 if b = false *)
	  c_nb <- Pke_indcpa.enc pk x (b ? r0 : r1); (* ciphertext c_{1-b}. Encrypt 0 using r0 if b = true, r1 if b = false *)

	  (* send commit message to verifier *)
	  send Fwd1.D.fw_req
	       (intport Verifier, (* Send this to Verifier *)
	       Encodings.epdp_commit_univ.`enc
	       (pt1, pt2, y, c_b, c_nb))
	  and transition WaitOpenReq(pt1, pt2, b, x, b ? r1 : r0, corrupted). (* For now, save the stuff that will be "opened" to V *)
	}
      | * => { fail. }
      end
    }

    state WaitOpenReq(pt1 : port, pt2 : port, b : bool, x : Cfptp.D, rb : Pke_indcpa.rand, corrupted : bool) {
      match message with
      | pt1'@Dir.Pt1.open_req => {
      	  if (pt1 = pt1') {
	    send Fwd2.D.fw_req
	       (intport Verifier,
	       Encodings.epdp_open_univ.`enc
	       (b, x, rb))
            and transition Final.
	  } else { fail. }
        }
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the committer is CORRUPTED *)
    (* --- --- --- --- --- ---  *)
    state WaitCrsCorrupted(pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      var fk : Cfptp.fkey;
      var pk : Pke_indcpa.pkey;

      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)
	  (* Ask the adversary for y, c_b, c_nb *)
	  send Adv.Pt1.adv_commit_msg_req(fk, pk)
	  and transition WaitAdvCommit(pt1, pt2, b, corrupted, fk, pk).
	}
      | * => { fail. }
      end
    }

    state WaitAdvCommit(pt1 : port, pt2 : port, b : bool, corrupted: bool, fk : Cfptp.fkey, pk : Pke_indcpa.pkey) {
      match message with
      | Adv.Pt1.adv_commit_msg_rsp(y', c_b', c_nb') => {
          send Fwd1.D.fw_req
	       (intport Verifier,
	       Encodings.epdp_commit_univ.`enc
	       (pt1, pt2, y', c_b', c_nb'))
	  and transition WaitOpenReqCorrupted(pt1, pt2, b, corrupted, y', c_b', c_nb'). (* For now, save everything. *)
      }
      | * => { fail. }
      end
    }

    state WaitOpenReqCorrupted(pt1 : port, pt2 : port, b : bool, corrupted : bool, y': Cfptp.D, c_b': Pke_indcpa.ciphertext, c_nb': Pke_indcpa.ciphertext) {
      match message with
      | pt1@Dir.Pt1.open_req => {
      	  (* Ask the adversary for y, c_b, c_nb *)
	  send Adv.Pt1.adv_gen_open_msg
	  and transition WaitAdvOpen(pt1, pt2, b, corrupted, y', c_b', c_nb').
        }
      | * => { fail. }
      end
    }

    state WaitAdvOpen(pt1 : port, pt2 : port, b : bool, corrupted : bool, y': Cfptp.D, c_b': Pke_indcpa.ciphertext, c_nb': Pke_indcpa.ciphertext) {
      match message with
      | Adv.Pt1.adv_open_msg(b', x', rb') => {
      	  send Fwd2.D.fw_req
	       (pt2,
	       Encodings.epdp_open_univ.`enc
	       (b', x', rb'))
          and transition Final.
        }
      | * => { fail. }
      end
    }

    state Final {
      match message with
      | * => { fail. }
      end
    }
  }

  party Verifier serves Dir.Pt2 Adv.Pt2 {

    initial state WaitCommit {
      var pt1, pt2 : port;
      var y : Cfptp.D;
      var c_b, c_nb : Pke_indcpa.ciphertext;
      match message with
      | Fwd1.D.fw_rsp(_, u) => { (* Verifier is activated after receiving a commit message *)
          match Encodings.epdp_commit_univ.`dec u with
          | Some tr => {
              (pt1, pt2, y, c_b, c_nb) <- tr;
              send Adv.Pt2.verifier_corrupted_req
	      and transition WaitCorruptionStatus(pt1, pt2, y, c_b, c_nb).
            }
          | None    => { fail. }  (* cannot happen *)
          end
        }
      | *                  => { fail. }
      end
    }

    state WaitCorruptionStatus(pt1 : port, pt2 : port, y : Cfptp.D, c_b : Pke_indcpa.ciphertext, c_nb : Pke_indcpa.ciphertext) {
      match message with
      | Adv.Pt2.verifier_corrupted_rsp( corrupted ) => { (* After receiving corruption status, do nothing (update later to allow V to send arbitrary messages to C *)
          send Dir.Pt2.commit_rsp(pt1)@pt2
	  and transition WaitOpen(pt1, pt2, y, c_b, c_nb, corrupted).
	}
      | * => { fail. }
      end
    }

    state WaitOpen(pt1 : port, pt2 : port, y : Cfptp.D, c_b : Pke_indcpa.ciphertext, c_nb : Pke_indcpa.ciphertext, corrupted : bool) {
      var b : bool;
      var x : Cfptp.D;
      var rb : Pke_indcpa.rand;
      match message with
      | Fwd2.D.fw_rsp(_, u) => {
          match Encodings.epdp_open_univ.`dec u with
          | Some tr => {
              (b, x, rb) <- tr;
              send Crs.Pt.crs_req
	      and transition WaitCrs(pt1, pt2, y, c_b, c_nb, corrupted, b, x, rb).
            }
          | None    => { fail. }  (* cannot happen *)
          end
        }
      | *                  => { fail. }
      end
    }

    state WaitCrs(pt1 : port, pt2 : port, y : Cfptp.D, c_b : Pke_indcpa.ciphertext, c_nb : Pke_indcpa.ciphertext, corrupted: bool,
b : bool, x : Cfptp.D, rb : Pke_indcpa.rand) {
      var y' : Cfptp.D;
      var c_b' : Pke_indcpa.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke_indcpa.pkey;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)

	  (* Do verification checks *)
	  y' <- Cfptp.forw fk x b;
	  c_b' <- Pke_indcpa.enc pk x rb;

	  if (y' = y /\ c_b = c_b') {
	    send Dir.Pt2.open_rsp(b)@pt2
	    and transition Final.
	  }
	  else { fail. }
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

}

(* Simulator *)
simulator Sim uses I2S simulates Real {

  initial state WaitCommitReq {
    match message with
    | I2S.commit_req(pt1, pt2) => { (* Committer asks commitment request *)
        send Real.Adv.Pt1.committer_corrupted  (* Ask adversary if Committer is corrupted *)
	and transition WaitCommitterCorruption(pt1, pt2). (* Wait to see if committer is corrupted *)
      }
    | * => { fail. }
    end
  }

  state WaitCommitterCorruption(pt1 : port, pt2 : port) {
    match message with
    | Real.Adv.Pt1.committer_corruption_status( pt1_corrupted ) => {
	send I2S.sim_committer_corruption(pt1_corrupted)
	and transition WaitIFCommitterCorruptMsg(pt1, pt2, pt1_corrupted).

      }
    | * => { fail. }
    end
  }

  state WaitIFCommitterCorruptMsg(pt1 : port, pt2 : port, pt1_corrupted : bool) {
    var data : port * port * bool;
    match message with
    | I2S.pt1_corrupted_input(u) => {
	match u with
	| Some b => { (* Receive corrupted committer's bit b *)
	    data <- (pt1, pt2, b);
	    send Real.Adv.Pt1.committer_corruption_data(Some data) (* Forward data to adversary *)
	    and transition WaitContinue(pt1, pt2, pt1_corrupted).
	  }
	| None => { (* For an honest committer, forward None to the adversary *)
	    send Real.Adv.Pt1.committer_corruption_data(None)
	    and transition WaitContinue(pt1, pt2, pt1_corrupted).
	  }
    	end
    }
    | * => { fail. }
    end
  }

  state WaitContinue(pt1: port, pt2: port, pt1_corrupted : bool) {
    var fk : Cfptp.fkey;
    var bk : Cfptp.bkey;
    var pk : Pke_indcpa.pkey;
    var sk : Pke_indcpa.skey;
    var crs : Cfptp.fkey * Pke_indcpa.pkey;
    match message with
    | Real.Adv.Pt1.continue => {
        (* Simulate the CRS ideal functionality *)
        (fk, bk) <$ Cfptp.keygen;
        (pk, sk) <$ Pke_indcpa.dkeygen;
	crs <- (fk, pk);

	if (pt1_corrupted) {
	  send Real.Crs.CrsI2S.crs_req(pt1, crs) (* Ask CRS's simulator to send crs to pt1 *)
	  and transition WaitCrsOkCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk).
	}
	else {
	  send Real.Crs.CrsI2S.crs_req(pt1, crs) (* Ask CRS's simulator to send crs to pt1 *)
	  and transition WaitCrsOk(pt1, pt2, pt1_corrupted, fk, bk, pk, sk).
	}
    }
    | * => { fail. }
    end
  }

  (* --- --- --- --- --- ---  *)
  (* States for when the committer is HONEST *)
  (* --- --- --- --- --- ---  *)

  state WaitCrsOk(pt1: port, pt2 : port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke_indcpa.pkey, sk : Pke_indcpa.skey) {
    var y, x0, x1 : Cfptp.D;
    var r0, r1 : Pke_indcpa.rand;
    var c0, c1 : Pke_indcpa.ciphertext;
    match message with
    | Real.Crs.CrsI2S.crs_rsp => {
      y <$ Cfptp.dD;
      x0 <- Cfptp.back bk y false;
      x1 <- Cfptp.back bk y true;
      r0 <$ Pke_indcpa.drand;
      r1 <$ Pke_indcpa.drand;
      c0 <- Pke_indcpa.enc pk x0 r0;
      c1 <- Pke_indcpa.enc pk x1 r1;

      (* send (pt1, pt2, y, c0, c1) to the adversary, who OKs forwarding to the verifier *)
      send Real.Fwd1.FwAdv.fw_obs
      	   (pt1, (* Sender is the Committer client pt1 *)
	   pt2,   (* Receiver is the Verifier client pt2*)
	   Encodings.epdp_commit_univ.`enc
	   (pt1, pt2, y, c0, c1))
      and transition WaitFwd1Ok(pt1, pt2, fk, pk, x0, x1, r0, r1). (* For less typing, I'm only remembering the state arguments required for open. *)
    }
    | * => { fail. }
    end
  }

  state WaitFwd1Ok(pt1 : port, pt2: port, fk : Cfptp.fkey, pk : Pke_indcpa.pkey, x0 : Cfptp.D, x1 : Cfptp.D, r0 : Pke_indcpa.rand, r1 : Pke_indcpa.rand) {
    match message with
    | Real.Fwd1.FwAdv.fw_ok => {
      send I2S.sim_commit_rsp(None) (* Tells ideal functionality commit message is OK'd by Forwarder. *)
      and transition WaitOpen(pt1, pt2, fk, pk, x0, x1, r0, r1).
    }
    | * => { fail. }
    end
  }

  state WaitOpen(pt1 : port, pt2: port, fk : Cfptp.fkey, pk : Pke_indcpa.pkey, x0 : Cfptp.D, x1 : Cfptp.D, r0 : Pke_indcpa.rand, r1 : Pke_indcpa.rand) {
    var b : bool;
    match message with
    | I2S.open_req(u) => {
      match u with
      | Some b' => {
          (* send (b', xb, rb) to the adversary, who OKs forwarding to the verifier *)
          send Real.Fwd2.FwAdv.fw_obs
      	  (pt1, (* Sender is the Committer client pt1 *)
	   pt2,   (* Recevier is the Verifier client pt2*)
	   Encodings.epdp_open_univ.`enc
	   (b', b' ? x1 : x0, b' ? r1 : r0))
      	  and transition WaitFwd2Ok(pt1, pt2, fk, pk, x0, x1, r0, r1).
      }
      | None => {
         (* If ideal functionality doesn't know this bit, sample a random one *)
	   b <$ {0,1};

      	   (* send (b, xb, rb) to the adversary, who OKs forwarding to the verifier *)
      	   send Real.Fwd2.FwAdv.fw_obs
      	   (pt1, (* Sender is the Committer client pt1 *)
	    pt2,   (* Recevier is the Verifier client pt2*)
	    Encodings.epdp_open_univ.`enc
	    (b, b ? x1 : x0, b ? r1 : r0))
     	   and transition WaitFwd2Ok(pt1, pt2, fk, pk, x0, x1, r0, r1).
      }
      end
    }
    | * => { fail. }
    end
  }

  state WaitFwd2Ok(pt1 : port, pt2: port, fk : Cfptp.fkey, pk : Pke_indcpa.pkey, x0 : Cfptp.D, x1 : Cfptp.D, r0 : Pke_indcpa.rand, r1 : Pke_indcpa.rand) {
    var crs : Cfptp.fkey * Pke_indcpa.pkey;
    match message with
    | Real.Fwd2.FwAdv.fw_ok => {
        crs <- (fk, pk);
        send Real.Crs.CrsI2S.crs_req(pt2, crs)
	and transition WaitVerifierCrsOk.
    }
    | * => { fail. }
    end
  }


  (* --- --- --- --- --- ---  *)
  (* States for when the committer is CORRUPTED *)
  (* --- --- --- --- --- ---  *)

  state WaitCrsOkCommitterCorrupted(pt1: port, pt2 : port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke_indcpa.pkey, sk : Pke_indcpa.skey) {
    match message with
    | Real.Crs.CrsI2S.crs_rsp => {
      (* Give the adversary the CRS string and ask it to generate the corrupted commit message *)
      send Real.Adv.Pt1.adv_commit_msg_req(fk, pk)
      and transition WaitAdvCommit(pt1, pt2, pt1_corrupted, fk, bk, pk, sk).
    }
    | * => { fail. }
    end
  }

  state WaitAdvCommit(pt1: port, pt2: port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke_indcpa.pkey, sk : Pke_indcpa.skey) {
    var x0, x1 : Pke_indcpa.plaintext;
    var x0', x1' : Cfptp.D;
    match message with
    | Real.Adv.Pt1.adv_commit_msg_rsp(y', c0', c1') => {
        (* Decrypt c0, c1 to compute x0, x1 *)
	x0 <- Pke_indcpa.dec sk c0';
	x1 <- Pke_indcpa.dec sk c1';
	(* Invert y' w.r.t. cfptp *)
	x0' <- Cfptp.back bk y' false;
	x1' <- Cfptp.back bk y' true;
	if (x0 = x0') {
	  send I2S.sim_commit_rsp(Some false) (* The adversary committed to b = false *)
	  and transition WaitOpenCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, Some false, y', c0', c1').
	}
	elif (x1 = x1') {
	  send I2S.sim_commit_rsp(Some true) (* The adversary committed to b = true *)
	  and transition WaitOpenCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, Some true, y', c0', c1').
	}
	else {
	  send I2S.sim_commit_rsp(None) (* The adversary sent a message that doesn't correspond to committing either 0 or 1 *)
	  and transition WaitOpenCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, None, y', c0', c1').
	}
    }
    | * => { fail. }
    end
  }

  state WaitOpenCommitterCorrupted(pt1: port, pt2: port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke_indcpa.pkey, sk : Pke_indcpa.skey, committed_b : bool option, y' : Cfptp.D, c0' : Pke_indcpa.ciphertext, c1' : Pke_indcpa.ciphertext) {
      match message with
      | I2S.open_req(b') => {
          (* Ask adversary for the committer's open message *)
          send Real.Adv.Pt1.adv_gen_open_msg
	  and transition WaitAdvOpen(pt1, pt2, fk, bk, pk, committed_b, y', c0', c1').
      }
      | * => { fail. }
      end
  }

  state WaitAdvOpen(pt1 : port, pt2 : port, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke_indcpa.pkey, committed_b : bool option, y' : Cfptp.D, c0' : Pke_indcpa.ciphertext, c1' : Pke_indcpa.ciphertext) {
      var x' : Cfptp.D;
      var ct : Pke_indcpa.ciphertext;
      var crs : Cfptp.fkey * Pke_indcpa.pkey;
      match message with
      | Real.Adv.Pt1.adv_open_msg(b', x, r) => {
          x' <- Cfptp.back bk y' b';
	  ct <- Pke_indcpa.enc pk x r;

	  crs <- (fk, pk);
	  if (x = x' /\ (b' ? c1' : c0') = ct) {
	    match committed_b with
	    | Some b => {
	        if (b' = b) {
	      	  send Real.Crs.CrsI2S.crs_req(pt2, crs)
	     	  and transition WaitVerifierCrsOk.
	        }
	    	else { fail. }
	    }
	    | None => { fail. }
	    end
	  }
	  else { fail. }
      }
      | * => { fail. }
      end
  }

  (* --- --- --- --- --- ---  *)
  (* End states - are the same regardless of if committer is corrupted or not *)
  (* --- --- --- --- --- ---  *)

  state WaitVerifierCrsOk { (* Emulate the verifier's call to the CRS ideal functionality *)
    match message with
    | Real.Crs.CrsI2S.crs_rsp => {
        send I2S.sim_open_rsp (* Tells ideal functionality that Forwarder OKs the open message. *)
	and transition Final.
    }
    | * => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
