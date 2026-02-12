(* Commitment.uc *)

(* This code models a two party UC Commitment scheme. It simplifies the scheme of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf) to only allow static corruption of the committer. This is a unit containing an ideal functionality, a real functionality (i.e. real protocol description), and a simulator. *)

(* Author: Megan Chen *)

(* Import required .uc files *)
uc_requires Forwarding Crs.

(* Import required easycrypt files. *)
ec_requires Cfptp Pke ForwardingEncodings View.

(* Direct interfaces, which are between ideal functionality and environment, from ideal functionality's perspective. Note that the ideal functionality emulates parties. *)
direct DirPt1 {  (* Party 1, i.e. the Committer *)
  in pt1@commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment of a value u to pt2 *)

  in pt1@open_req  (* message to pt2, asking to send the opening of the commitment to pt2 *)

  (* Corruption status messages *)
  in pt1@committer_corruption_status_req (* pt1 asks whether Committer is corrupted *)

  out committer_corruption_status_rsp( corrupted : bool )@pt1 (* tells pt1 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)
}

direct DirPt2 {  (* Party 2, i.e. the Verifier *)
  out commit(pt1 : port)@pt2  (* message to pt2, saying that pt1 has committed a message u *)

  out open(u : bool)@pt2  (* message to pt2, saying that pt1 sent u to it *)

  (* Corruption status messages *)
  in pt2@verifier_corruption_status_req (* pt2 asks whether this party is corrupted *)

  out verifier_corruption_status_rsp( corrupted : bool )@pt2 (* tells pt2 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)

}

direct Dir {
  Pt1 : DirPt1  (* Party 1 *)
  Pt2 : DirPt2  (* Party 2 *)

}

(* Interface between ideal functionality and
   simulator, viewed from ideal functionality *)
adversarial I2S {

  (* Commit phase *)
  out commit_req(pt1 : port, pt2 : port) (* Send both parties' port addresses to the simulator, where pt1 is the committer and pt2 is the verifier. *)

  in commit_ok(u' : bool option) (* Simulator OKs sending a commit message to pt2. It also has the option of detecting u' and returning it. *)

  (* Initial corruption sequence *)
  in committer_corruption_status_rsp(pt1_corrupted : bool) (* Receive from simulator whether each port pt is corrupted. True = corrupted. False = honest. *)

  out committer_bit(u : bool option) (* If pt1 is corrupted, send its boolean input u to the simulator. Otherwise, send None. Note that pt2 has no input. *)

  (* Open phase *)
  out open_req(b' : bool) (* open message request from ideal functionality to simulator. If it knows the bit b' to be opened, return it. *)

  in open_ok (* simulator OKs sending a open message to pt2, conveying no additional information. Otherwise, send None. *)

  (* Corruption later in execution *)
  in corrupt_committer (* Simulator tells ideal functionality that committer has become corrupted *)

  out corrupt_committer_ack(b : bool) (* If pt1 becomes corrupted, send the committed bit b to the simulator *)

  in corrupt_verifier (* Simulator tells ideal functionality that verifier has become corrupted *)

  out corrupt_verifier_ack (* IF acks that verifier is corrupted *)

}

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
    | I2S.committer_corruption_status_rsp(pt1_corrupted) => {
        send I2S.committer_bit( pt1_corrupted ? (Some b) : (None) ) (* If pt1 is corrupted, send its input to the simulator. Otherwise send None. *)
        and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted). (* Transition to whether Sim OKs pt1's commit request *)
      }
    | pt1'@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
        if (pt1' = pt1) {
          send Dir.Pt1.committer_corruption_status_rsp( false )@pt1 (* send pt1's corruption status *)
    	  and transition WaitCorruptions(b, pt1, pt2). (* return to this same state *)
        }
        else {
          fail.
        }
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
    | I2S.commit_ok(b') => { (* b' is None if committer is not corrupted and if simulator doesn't know the committed bit. *)
        send Dir.Pt2.commit(pt1)@pt2  (* Deliver pt1's commitment message to pt2, which excludes the commited value u *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, b').   (* Transition to waiting for pt1's open message *)
      }
    | I2S.corrupt_committer => { (* Simulator tells ideal functionality that the committer has been corrupted *)
        send I2S.corrupt_committer_ack(b) (* Ideal functionality sends the committed bit to simulator *)
	and transition WaitCommitRsp(b, pt1, pt2, true). (* return to this same state, but with pt1_corrupted = true *)
      }
    | pt1'@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
        if (pt1' = pt1) {
          send Dir.Pt1.committer_corruption_status_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted). (* return to this same state *)
	}
	else {
	  fail.
	}
      }
    | * => { fail. }
    end
  }

  state WaitOpenReq(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, b' : bool option) {
    match message with
    (* Pt1 attempts to send an open message to pt2. Message is adversarially delayed, i.e. forwarded to Sim, who oks delivery. *)
    | pt1'@Dir.Pt1.open_req => {
        if (pt1' = pt1) {
          send I2S.open_req(b)  (* Ask simulator whether to deliver pt1's open message to pt2. Tell it the bit to be opened. *)
     	  and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, b'). (* Transition to waiting for simulator's response *)
        }
        else {
          fail.
        }
      }
    | pt1'@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
        if (pt1' = pt1) {
          send Dir.Pt1.committer_corruption_status_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, b'). (* return to this same state *)
	}
	else {
	  fail.
	}
      }
    | * => { fail. }
    end
  }

  state WaitOpenRsp(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, b' : bool option) {
    match message with
    (* Simulator oks delivery of pt1's open message, which includes b, to pt2. *)
    | I2S.open_ok => {
        match b' with
          | Some b' => {
	      send Dir.Pt2.open(b')@pt2
	      and transition Final(pt1, pt1_corrupted).
	    }
	  | None => { (* Note: If committer is corrupted and the ideal functionality receives b' = None from the simulator in the commit round, the simulator will never send open_ok, so the following message won't occur. *)
	      send Dir.Pt2.open(b)@pt2
	      and transition Final(pt1, pt1_corrupted).
	    }
	  end
      }
    | I2S.corrupt_committer => { (* Simulator tells ideal functionality that the committer has been corrupted *)
        send I2S.corrupt_committer_ack(b) (* Ideal functionality sends the committed bit to simulator. Note that sending the bit isn't necessarily here, but is included for a simpler interface. *)
	and transition WaitOpenRsp(b, pt1, pt2, true, b'). (* Return to this same state, but with pt1_corrupted = true *)
      }
    | pt1'@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
        if (pt1' = pt1) {
          send Dir.Pt1.committer_corruption_status_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, b'). (* return to this same state *)
	}
	else {
	  fail.
	}
      }
    | * => { fail. }
    end
  }

  state Final(pt1 : port, pt1_corrupted : bool) {
    match message with
    | pt1'@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
        if (pt1' = pt1) {
          send Dir.Pt1.committer_corruption_status_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	  and transition Final(pt1, pt1_corrupted). (* return to this same state *)
	}
	else {
	  fail.
	}
      }
    | * => { fail. }
    end
  }
}

(* Adversarial interfaces between a real party and the adversary, from the perspective of the real party *)
adversarial Pt1Adv {

  (* Party corruption messages *)
  out committer_corruption_status_req (* Ask adversary if the committer is corrupted *)

  in committer_corruption_status_rsp( corrupted : bool ) (* corrupted = true if corrupted. corrupted = false if the party is honest *)

  in corrupt (* Adv tells Pt1 it is corrupted, after initial corruption sequence *)

  out send_view(cview : (View.committer) option) (* sends None if committer is not corrupted. Sends all known data if committer is corrupted.*)

  in continue (* Adv response message that returns control to committer *)

  (* Post-corruption messages with the adversary *)
  out commit_msg_req(cview: View.committer) (* Forward updated view (including CRS) to the adversary *)

  in commit_msg_rsp(y': Cfptp.D, c_b': Pke.ciphertext, c_nb': Pke.ciphertext) (* Adv responds with the y, c_b, c_bn values it wants to send to the verifier *)

  out open_msg_req (* Ask adv for the open message *)

  in open_msg_rsp(b' : bool, x' : Cfptp.D, r_b' : Pke.rand, r_nb' : Pke.rand)
}

adversarial Pt2Adv {

  (* Initial corruption sequence *)
  out verifier_corruption_status_req (* Ask adversary if the verifier is corrupted *)

  in verifier_corruption_status_rsp( corrupted : bool ) (* corrupted = true if corrupted. corrupted = false if the party is honest *)

  in continue (* Adv response message that returns control to verifier *)

  (* Adversary corruptions after initial *)
  in corrupt (* adversary tells Pt1 it is corrupted *)

  out send_view (vview : (View.verifier) option) (* send the verifier's view thus far to the adversary *)

  (* Post-corruption messages with the adversary *)
  out output_bit_req(vview: View.verifier) (* Forward updated view to the adversary *)

  in output_bit_rsp(b : bool) (* Adv responds with output bit b *)
}

(* Composite adversarial interface between parties and adversary *)
adversarial Adv {
  Pt1 : Pt1Adv (* Adversary that talks to Pt1 *)
  Pt2 : Pt2Adv (* Adversary that talks to Pt2 *)
}

(* Real Protocol *)
functionality Real implements Dir Adv {
  subfun Fwd1 = Forwarding.Forw (* For commit phase *)
  subfun Fwd2 = Forwarding.Forw (* For open phase *)
  subfun Crs = Crs.Ideal

  party Committer serves Dir.Pt1 Adv.Pt1 {
    initial state WaitCommReq {
      var cview : View.committer;
      match message with
      | pt1@Dir.Pt1.commit_req(pt2, b) => {
	  cview <- [View.C_c_env_port pt1; View.C_v_env_port pt2; View.C_env_b b]; (* initialize list and add elts *)
	  send Adv.Pt1.committer_corruption_status_req (* Ask adversary about committer's corruption status *)
	  and transition WaitCorruptionStatus(cview, pt1, pt2, b).
	}
      | * => { fail. }
      end
    }

    state WaitCorruptionStatus(cview : View.committer, pt1 : port, pt2 : port, b : bool) {
      match message with
      | Adv.Pt1.committer_corruption_status_rsp( corrupted ) => {
          send Adv.Pt1.send_view( corrupted ? Some(cview) : None)
	  and transition WaitContinue(cview, pt1, pt2, b, corrupted).
	}
      | pt1'@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          if (pt1' = pt1) {
            send Dir.Pt1.committer_corruption_status_rsp( false )@pt1 (* send pt1's corruption status *)
    	    and transition WaitCorruptionStatus(cview, pt1, pt2, b). (* return to this same state *)
          }
          else {
            fail.
          }
      }
      | * => { fail. }
      end
    }

    state WaitContinue(cview : View.committer, pt1 : port, pt2 : port, b: bool, corrupted : bool) {
      (*var new_cview : View.committer;*)
      match message with
      | Adv.Pt1.continue => {
      	  if (corrupted) {
	    send Crs.Pt.crs_req (* request CRS *)
	    and transition WaitCrs_Corrupted(cview, pt1, pt2, b, corrupted). (* Go to states modelling corrupted committer *)
	  }
	  else { (* Committer honest *)
	    send Crs.Pt.crs_req (* request CRS *)
	    and transition WaitCrs(cview, pt1, pt2, b, corrupted). (* Go to states modelling honest committer *)
	  }
	}
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitContinue(cview, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | Adv.Pt1.corrupt => {
      	  send Adv.Pt1.send_view(Some cview)
	  and transition WaitContinue(cview, pt1, pt2, b, true). (* updated corrupted bit to true *)
        }
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the committer is HONEST *)
    (* --- --- --- --- --- ---  *)
    state WaitCrs(cview: View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      var new_cview : View.committer;
      var x : Cfptp.D;
      var r, r_sample : Pke.rand;
      var y : Cfptp.D;
      var c_b, c_nb : Pke.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      var c_vals : Types.commit_vals;
      var o_vals : Types.open_vals;
      var r_fake : Types.open_rfake;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)

	  (* generate commit message *)
	  x <$ Pke.dplaintext;
	  r <$ Pke.drand;
	  r_sample <$ Pke.drand;
	  o_vals <- (x, r); (* These values will be sent later for opening *)
	  r_fake <- r_sample;

	  y <- Cfptp.forw fk x b; (* compute f_b(x), where f_b is a cfptp. *)
	  c_b <- Pke.enc pk x r; (* ciphertext c_b. Encrypt x using r *)
	  c_nb <- Pke.oblivenc pk r_sample; (* ciphertext c_{1-b}. Obliviously encrypt to generate a ciphertext using randomness r *)
	  c_vals <- b ? (y, c_nb, c_b) : (y, c_b, c_nb); (* record (y, c0, c1) *)

	  (* Add everything to the committer's view *)
	  new_cview <- cview ++ [View.C_crs crs] (* CRS *)
	  	      	   ++ [View.C_omsg o_vals; View.C_omsg_rfake r_fake] (* open message values *)
			   ++ [View.C_cmsg c_vals]; (* commit message values *)
	  (* send commit message to verifier *)
	  send Fwd1.D.fw_req
	       (intport Verifier, (* Send this to Verifier *)
	        ForwardingEncodings.epdp_commit_univ.`enc
	        ( b ? (pt1, pt2, y, c_nb, c_b) : (pt1, pt2, y, c_b, c_nb) )
	       )
	  and transition WaitOpenReq(new_cview, pt1, pt2, b, corrupted, o_vals, r_fake).
	}
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitCrs(cview, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitOpenReq(cview : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool, o_vals : Types.open_vals, r_fake : Types.open_rfake) {
      var new_cview : View.committer;
      var x : Cfptp.D; var r : Pke.rand;
      var r_sample : Pke.rand;
      match message with
      | pt1'@Dir.Pt1.open_req => {
      	  if (pt1 = pt1') {
	    new_cview <- cview ++ [View.C_open_c_env_port pt1'];
	    (x,r) <- o_vals;
	    r_sample <- r_fake;
	    send Fwd2.D.fw_req
	       (intport Verifier,
	       ForwardingEncodings.epdp_open_univ.`enc
	       (b, x, r, r_sample))
            and transition Final(new_cview, corrupted).
	  } else { fail. }
        }
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitOpenReq(cview, pt1, pt2, b, corrupted, o_vals, r_fake). (* return to this same state *)
   	}
      | Adv.Pt1.corrupt => {
      	  send Adv.Pt1.send_view(Some cview)
	  and transition WaitOpenReq_Corrupted(cview, pt1, pt2, b, true). (* updated corrupted bit to true *)
        }
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the committer is CORRUPTED *)
    (* --- --- --- --- --- ---  *)
    state WaitCrs_Corrupted(cview : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      var new_cview : View.committer;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse CRS *)
	  new_cview <- cview ++ [View.C_crs crs];
	  (* Ask the adversary for y, c_false, c_true *)
	  send Adv.Pt1.commit_msg_req(new_cview)
	  and transition WaitAdvCommit(new_cview, pt1, pt2, b, corrupted).
	}
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitCrs_Corrupted(cview, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitAdvCommit(cview: View.committer, pt1 : port, pt2 : port, b : bool, corrupted: bool) {
      match message with
      | Adv.Pt1.commit_msg_rsp(y', c_false', c_true') => {
          send Fwd1.D.fw_req
	       (intport Verifier,
	       ForwardingEncodings.epdp_commit_univ.`enc
	       (pt1, pt2, y', c_false', c_true'))
	  and transition WaitOpenReq_Corrupted(cview, pt1, pt2, b, corrupted).
      }
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitAdvCommit(cview, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitOpenReq_Corrupted(cview : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      match message with
      | pt1'@Dir.Pt1.open_req => {
      	  if (pt1 = pt1') { (* Assume that only the committing port can request openings *)
	    (* Ask the adversary for b, x, r_bool *)
	    send Adv.Pt1.open_msg_req
	    and transition WaitAdvOpen(cview, pt1, pt2, b, corrupted).
	  } else { fail. }
        }
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitOpenReq_Corrupted(cview, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitAdvOpen(cview : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      match message with
      | Adv.Pt1.open_msg_rsp(b', x', r_b', r_nb') => {
      	  send Fwd2.D.fw_req
	       (intport Verifier,
	       ForwardingEncodings.epdp_open_univ.`enc
	       (b', x', r_b', r_nb'))
          and transition Final(cview, corrupted).
        }
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitAdvOpen(cview, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state Final(cview: View.committer, corrupted : bool) {
      match message with
      | pt1@Dir.Pt1.committer_corruption_status_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corruption_status_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition Final(cview, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }
  }

  party Verifier serves Dir.Pt2 Adv.Pt2 {

    initial state WaitCommit {
      var vview : View.verifier;
      var pt1, pt2 : port;
      var y : Cfptp.D;
      var c_false, c_true : Pke.ciphertext;
      var c_vals : Types.commit_vals;
      match message with
      | Fwd1.D.fw_rsp(_, u) => { (* Verifier is activated after receiving a commit message *)
          match ForwardingEncodings.epdp_commit_univ.`dec u with
          | Some tr => {
              (pt1, pt2, y, c_false, c_true) <- tr;
	      c_vals <- (y, c_false, c_true);
	      vview <- [View.V_c_env_port pt1; View.V_v_env_port pt2; View.V_cmsg c_vals];
              send Adv.Pt2.verifier_corruption_status_req
	      and transition WaitCorruptionStatus(vview, pt1, pt2, c_vals).
            }
          | None => { fail. }  (* cannot happen *)
          end
        }
      | * => { fail. }
      end
    }

    state WaitCorruptionStatus(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals) {
      match message with
      | Adv.Pt2.verifier_corruption_status_rsp( corrupted ) => { (* After receiving corruption status, do nothing (update later to allow V to send arbitrary messages to C *)
	  send Adv.Pt2.send_view( corrupted ? Some(vview) : None)
	  and transition WaitContinue(vview, pt1, pt2, c_vals, corrupted).
	}
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( false )@pt2 (* send pt2's corruption status *)
  	  and transition WaitCorruptionStatus(vview, pt1, pt2, c_vals). (* return to this same state *)
      }
      | * => { fail. }
      end
    }

    state WaitContinue(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted : bool) {
      match message with
      | Adv.Pt2.continue => {
      	if (corrupted) {
	  send Dir.Pt2.commit(pt1)@pt2
	  and transition WaitOpen_Corrupted(vview, pt1, pt2, c_vals, corrupted).
	}
	else {
          send Dir.Pt2.commit(pt1)@pt2
	  and transition WaitOpen(vview, pt1, pt2, c_vals, corrupted).
	}
      }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitContinue(vview, pt1, pt2, c_vals, corrupted). (* return to this same state *)
      }
      | Adv.Pt2.corrupt => {
      	  send Adv.Pt2.send_view(Some vview)
	  and transition WaitContinue(vview, pt1, pt2, c_vals, true). (* updated corrupted bit to true *)
      }
      | * => { fail. }
      end
    }

    state WaitOpen(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted : bool) {
      var new_vview : View.verifier;
      var b : bool;
      var x : Cfptp.D;
      var r_b, r_nb : Pke.rand;
      var o_vals : Types.open_vals;
      var r_fake : Types.open_rfake;
      match message with
      | Fwd2.D.fw_rsp(_, u) => {
          match ForwardingEncodings.epdp_open_univ.`dec u with
          | Some tr => {
              (b, x, r_b, r_nb) <- tr;
	      o_vals <- (x, r_b);
	      r_fake  <- r_nb;
	      new_vview <- vview ++ [View.V_omsg_b b; View.V_omsg o_vals; View.V_omsg_rfake r_fake];
              send Crs.Pt.crs_req
	      and transition WaitCrs(new_vview, pt1, pt2, c_vals, corrupted, b, o_vals).
            }
          | None => { fail. }  (* cannot happen *)
          end
        }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitOpen(vview, pt1, pt2, c_vals, corrupted). (* return to this same state *)
      }
      | Adv.Pt2.corrupt => {
      	  send Adv.Pt2.send_view(Some vview)
	  and transition WaitOpen_Corrupted(vview, pt1, pt2, c_vals, true). (* updated corrupted bit to true *)
      }
      | * => { fail. }
      end
    }

    state WaitCrs(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted: bool, b : bool, o_vals : Types.open_vals) {
      var new_vview : View.verifier;
      var y' : Cfptp.D;
      var c' : Pke.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      var y : Cfptp.D; var c_false, c_true : Pke.ciphertext; (* Commit msg *)
      var x : Cfptp.D; var r : Pke.rand;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)
	  new_vview <- vview ++ [View.V_crs crs];

	  (* parse messages *)
	  (y, c_false, c_true) <- c_vals;
	  (x, r) <- o_vals;
	  (* Do verification checks *)
	  y' <- Cfptp.forw fk x b;
	  c' <- Pke.enc pk x r;

	  if (y' = y /\ (b ? (c' = c_true) : (c' = c_false) )) {
	    send Dir.Pt2.open(b)@pt2
	    and transition Final(new_vview).
	  }
	  else { fail. }
        }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitCrs(vview, pt1, pt2, c_vals, corrupted, b, o_vals). (* return to this same state *)
      }
      | Adv.Pt2.corrupt => {
      	  send Adv.Pt2.send_view(Some vview)
	  and transition WaitCrs_Corrupted(vview, pt1, pt2, c_vals, true, b, o_vals). (* updated corrupted bit to true *)
      }
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the verifier is CORRUPTED *)
    (* --- --- --- --- --- ---  *)

    state WaitOpen_Corrupted(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted : bool) {
      var new_vview : View.verifier;
      var b : bool;
      var x : Cfptp.D;
      var r_b, r_nb : Pke.rand;
      var o_vals : Types.open_vals;
      var r_fake : Types.open_rfake;
      match message with
      | Fwd2.D.fw_rsp(_, u) => {
        match ForwardingEncodings.epdp_open_univ.`dec u with
          | Some tr => {
              (b, x, r_b, r_nb) <- tr;
	      o_vals <- (x, r_b);
	      r_fake  <- r_nb;
	      new_vview <- vview ++ [View.V_omsg_b b; View.V_omsg o_vals; View.V_omsg_rfake r_fake];
              send Adv.Pt2.send_view(Some(new_vview))
	      and transition WaitAdvContinue(vview, pt1, pt2, c_vals, true, b, o_vals).
            }
          | None => { fail. }  (* cannot happen *)
          end
      }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitOpen_Corrupted(vview, pt1, pt2, c_vals, corrupted). (* return to this same state *)
      }
      | * => { fail. }
      end
    }

    state WaitAdvContinue(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted: bool, b : bool, o_vals : Types.open_vals) {
      match message with
      | Adv.Pt2.continue => {
          send Crs.Pt.crs_req
	  and transition WaitCrs_Corrupted(vview, pt1, pt2, c_vals, corrupted, b, o_vals).
      }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitAdvContinue(vview, pt1, pt2, c_vals, corrupted, b, o_vals). (* return to this same state *)
      }
      | * => { fail. }
      end
    }

    state WaitCrs_Corrupted(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted: bool, b : bool, o_vals : Types.open_vals) {
      var new_vview : View.verifier;
      var y' : Cfptp.D;
      var c' : Pke.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      var y : Cfptp.D; var c_false, c_true : Pke.ciphertext; (* Commit msg *)
      var x : Cfptp.D; var r : Pke.rand;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
          new_vview <- vview ++ [View.V_crs crs];
	  send Adv.Pt2.output_bit_req(new_vview)
	  and transition WaitAdvOutputBit(new_vview, pt1, pt2, c_vals, corrupted, b, o_vals).
      }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitCrs_Corrupted(vview, pt1, pt2, c_vals, corrupted, b, o_vals). (* return to this same state *)
      }
      | * => { fail. }
      end
    }

    state WaitAdvOutputBit(vview : View.verifier, pt1 : port, pt2 : port, c_vals : Types.commit_vals, corrupted: bool, b : bool, o_vals : Types.open_vals) {
      match message with
      | Adv.Pt2.output_bit_rsp(b) => {
          send Dir.Pt2.open(b)@pt2
	  and transition Final(vview).
      }
      | pt2@Dir.Pt2.verifier_corruption_status_req => { (* pt2 asks if it is corrupted *)
          send Dir.Pt2.verifier_corruption_status_rsp( corrupted )@pt2 (* send pt2's corruption status *)
  	  and transition WaitAdvOutputBit(vview, pt1, pt2, c_vals, corrupted, b, o_vals). (* return to this same state *)
      }
      | * => { fail. }
      end
    }

    state Final(vview : View.verifier) {
      match message with
      | * => { fail. }
      end
    }
  }

}

(* Simulator *)
simulator Sim uses I2S simulates Real {

  initial state WaitCommitReq {
    var cview : View.committer;
    match message with
    | I2S.commit_req(pt1, pt2) => { (* Committer asks commitment request *)
        cview <- [View.C_c_env_port pt1; View.C_v_env_port pt2];
        send Real.Adv.Pt1.committer_corruption_status_req  (* Ask adversary if Committer is corrupted *)
	and transition WaitCommitterCorruption(cview, pt1, pt2). (* Wait to see if committer is corrupted *)
      }
    | * => { fail. }
    end
  }

  state WaitCommitterCorruption(cview : View.committer, pt1 : port, pt2 : port) {
    match message with
    | Real.Adv.Pt1.committer_corruption_status_rsp( pt1_corrupted ) => {
	send I2S.committer_corruption_status_rsp(pt1_corrupted)
	and transition WaitIFCommitterCorruptMsg(cview, pt1, pt2, pt1_corrupted).
      }
    | * => { fail. }
    end
  }

  state WaitIFCommitterCorruptMsg(cview : View.committer, pt1 : port, pt2 : port, pt1_corrupted : bool) {
    var new_cview : View.committer;
    match message with
    | I2S.committer_bit(bit) => {
	match bit with
	| Some b => { (* Receive corrupted committer's bit b *)
	    new_cview <- cview ++ [View.C_env_b b];
	    send Real.Adv.Pt1.send_view(Some new_cview) (* Forward data to adversary *)
	    and transition WaitContinue(new_cview, pt1, pt2, pt1_corrupted, Some b).
	  }
	| None => { (* For an honest committer, forward None to the adversary *)
	    send Real.Adv.Pt1.send_view(None)
	    and transition WaitContinue(cview, pt1, pt2, pt1_corrupted, None).
	  }
    	end
    }
    | * => { fail. }
    end
  }

  state WaitContinue(cview : View.committer, pt1: port, pt2: port, pt1_corrupted : bool, committer_bit : bool option) {
    var fk : Cfptp.fkey;
    var bk : Cfptp.bkey;
    var pk : Pke.pkey;
    var sk : Pke.skey;
    var crs : Types.crs;
    var sim_crs : Types.sim_crs;
    var new_cview : View.committer;
    match message with
    | Real.Adv.Pt1.continue => {
        (* Simulate the CRS ideal functionality *)
        (fk, bk) <$ Cfptp.keygen;
        (pk, sk) <$ Pke.dkeygen;
	crs <- (fk, pk);
	sim_crs <- (fk, bk, pk, sk);
	new_cview <- cview ++ [View.C_crs crs];
	match committer_bit with
	| Some committer_b => { (* i.e. pt1_corrupted = true *)
	    send Real.Crs.Adv.crs_send_req(intport Real.Committer, crs) (* Ask adversary to send crs to the Committer *)
	    and transition WaitCrsOkCommitter_Corrupted(new_cview, pt1, pt2, pt1_corrupted, sim_crs, committer_b).
	  }
	| None => { (* i.e. pt1_corrupted = false *)
	    send Real.Crs.Adv.crs_send_req(intport Real.Committer, crs) (* Ask adversary to send crs to the Committer *)
	    and transition WaitCrsOk(new_cview, pt1, pt2, pt1_corrupted, sim_crs).
	  }
	end
    }
    | Real.Adv.Pt1.corrupt => {
        send I2S.corrupt_committer
	and transition WaitContinue_IFAckCommitterCorrupted(cview, pt1, pt2, true). (* Set pt1_corrupted = true *)
      }
    | * => { fail. }
    end
  }



  state WaitContinue_IFAckCommitterCorrupted(cview : View.committer, pt1: port, pt2 : port, pt1_corrupted : bool){
    var new_cview : View.committer;
    match message with
    | I2S.corrupt_committer_ack(b) => {
        new_cview <- cview ++ [View.C_env_b b];
    	send Real.Adv.Pt1.send_view(Some cview)
	and transition WaitContinue(cview, pt1, pt2, pt1_corrupted, Some b). (* updated corrupted bit to true *)
    }
    | * => { fail. }
    end
  }

  (* --- --- --- --- --- ---  *)
  (* States for when the committer is HONEST *)
  (* --- --- --- --- --- ---  *)

  state WaitCrsOk(cview : View.committer, pt1: port, pt2 : port, pt1_corrupted : bool, sim_crs : Types.sim_crs) {
    var y, x0, x1 : Cfptp.D;
    var r0, r1 : Pke.rand;
    var c0, c1 : Pke.ciphertext;
    var pt1_corrupted' : bool;
    var fk : Cfptp.fkey;
    var bk : Cfptp.bkey;
    var pk : Pke.pkey;
    var sk : Pke.skey;
    var c_vals : Types.commit_vals;
    var o_vals_sim : Types.open_vals_sim;
    var new_cview : View.committer;
    match message with
    | Real.Crs.Adv.crs_send_ok => {

      (fk, bk, pk, sk) <- sim_crs;
      y <$ Cfptp.dD;
      x0 <- Cfptp.back bk y false;
      x1 <- Cfptp.back bk y true;

      r0 <$ Pke.drand;
      r1 <$ Pke.drand;
      c0 <- Pke.enc pk x0 r0;
      c1 <- Pke.enc pk x1 r1;

      (* this is r_false below
      r0' <- oblivenc_inv pk c0;
      r1' <- oblivenc_inv pk c1;
      *)

      c_vals <- (y, c0, c1);
      o_vals_sim <- (x0, x1, r0, r1);

      new_cview <- cview ++ [View.C_cmsg c_vals];
      (* send (pt1, pt2, y, c0, c1) to the adversary, who OKs forwarding to the verifier *)
      send Real.Fwd1.FwAdv.fw_obs
      	   (intport Real.Committer, (* Sender is the Committer *)
	    intport Real.Verifier,   (* Receiver is the Verifier *)
	    ForwardingEncodings.epdp_commit_univ.`enc
	    (pt1, pt2, y, c0, c1))
      and transition WaitFwd1Ok(new_cview, pt1, pt2, pt1_corrupted, sim_crs, c_vals, o_vals_sim).
    }
    | Real.Adv.Pt1.corrupt => { (* Adversary corrupts the committer *)
        pt1_corrupted' <- true;
	send I2S.corrupt_committer
	and transition WaitCrsOkCommitter_IFAckCommitterCorrupted(cview, pt1, pt2, pt1_corrupted', sim_crs).
      }
    | * => { fail. }
    end
  }

  state WaitCrsOkCommitter_IFAckCommitterCorrupted(cview : View.committer, pt1: port, pt2 : port, pt1_corrupted : bool, sim_crs : Types.sim_crs){
    var pt1_corrupted' : bool;
    var new_cview : View.committer;
    match message with
    | I2S.corrupt_committer_ack(b) => {
        new_cview <- cview ++ [View.C_env_b b];
        send Real.Adv.Pt1.send_view(Some new_cview)
	and transition WaitCrsOkCommitter_Corrupted(cview, pt1, pt2, pt1_corrupted, sim_crs, b).
    }
    | * => { fail. }
    end
  }

  state WaitFwd1Ok(cview : View.committer, pt1 : port, pt2: port, pt1_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim) {
    var commit_msg_status : bool; (* whether or not we send an honest commit message *)
    var pt1_corrupted' : bool;
    var pt2_corrupted : bool;
    var vview : View.verifier;
    match message with
    | Real.Fwd1.FwAdv.fw_ok => {
      commit_msg_status <- true; (* Record that an HONEST commitment message was sent *)
      vview <- [View.V_c_env_port pt1; View.V_v_env_port pt2; View.V_cmsg c_vals]; (* Verifier's view. Note that verifier is 1st activated here, after receiving the commit message. *)
      pt2_corrupted <- false;
      send I2S.commit_ok(None) (* Tells ideal functionality commit message is OK'd by Forwarder, and the simulator doesn't know the committed bit. *)
      and transition WaitOpen(cview, pt1, pt2, pt1_corrupted, pt2_corrupted, sim_crs, c_vals, o_vals_sim, commit_msg_status, vview).
    }
    | Real.Adv.Pt1.corrupt => { (* Adversary can corrupt here and modify the commit message *)
        pt1_corrupted' <- true;
	send I2S.corrupt_committer
	and transition WaitFwd1Ok_IFAckCommitterCorrupted(cview, pt1, pt2, pt1_corrupted', sim_crs, c_vals, o_vals_sim).
      }
    | * => { fail. }
    end
  }

  state WaitFwd1Ok_IFAckCommitterCorrupted(cview : View.committer, pt1 : port, pt2: port, pt1_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim) {
    var new_cview : View.committer;
    match message with
    | I2S.corrupt_committer_ack(b) => {
        new_cview <- cview ++ [View.C_env_b b];
        send Real.Adv.Pt1.send_view(Some cview)
	and transition WaitAdvCommit(cview, pt1, pt2, pt1_corrupted, sim_crs, b). (* Adversary never forwards the commitment message, allow adversary to choose the message *)
    }
    | * => { fail. }
    end
  }

  state WaitOpen(cview : View.committer, pt1 : port, pt2: port, pt1_corrupted : bool, pt2_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim, commit_msg_status : bool, vview : View.verifier) {
    var r_fake : Pke.rand;
    var pt1_corrupted' : bool;
    var fk : Cfptp.fkey; var bk : Cfptp.bkey; var pk : Pke.pkey; var sk : Pke.skey; (* Simulated CRS *)
    var y : Cfptp.D; var c0, c1 : Pke.ciphertext; (* Commit msg *)
    var x0, x1 : Cfptp.D; var r0, r1 : Pke.rand; (* Open msg values *)
    var new_cview : View.committer;
    var o_vals : Types.open_vals;
    match message with
    | I2S.open_req(b') => {
        (* Parse *)
        (fk, bk, pk, sk) <- sim_crs;
	(y, c0, c1) <- c_vals;
	(x0, x1, r0, r1) <- o_vals_sim;

        (* compute randomness associated with c_nb *)
	if (b' = true) {
	  r_fake <- Pke.oblivenc_inv pk c0;
	}
	else {
	  r_fake <- Pke.oblivenc_inv pk c1;
	}

	o_vals <- ((b' ? x1 : x0), (b' ? r1 : r0));
	new_cview <- cview ++ [View.C_omsg o_vals];

        (* send (b', xb, r_bool, r_fake) to the adversary, who OKs forwarding to the verifier *)
        send Real.Fwd2.FwAdv.fw_obs
      	(intport Real.Committer, (* Sender is the Committer *)
	 intport Real.Verifier,   (* Receiver is the Verifier *)
	 ForwardingEncodings.epdp_open_univ.`enc
	 (b', (b' ? x1 : x0), (b' ? r1 : r0), r_fake)
	)
      	and transition WaitFwd2Ok(cview, pt1, pt2, pt1_corrupted, pt2_corrupted, sim_crs, c_vals, o_vals_sim, r_fake, commit_msg_status, vview, b').
    }
    | Real.Adv.Pt1.corrupt => { (* Adversary can corrupt when control returns to environment (and prior to receiving open_req *)
        pt1_corrupted' <- true;
	send I2S.corrupt_committer
	and transition WaitOpen_IFAckCommitterCorrupted(cview, pt1, pt2, pt1_corrupted', pt2_corrupted, sim_crs, c_vals, o_vals_sim, commit_msg_status, vview).
      }
    | Real.Adv.Pt2.corrupt => { (* Adversary can corrupt when control returns to environment (and prior to receiving open_req *)
	send I2S.corrupt_verifier
	and transition WaitOpen_IFAckVerifierCorrupted(cview, pt1, pt2, pt1_corrupted, true, sim_crs, c_vals, o_vals_sim, commit_msg_status, vview).
      }
    | * => { fail. }
    end
  }

  state WaitOpen_IFAckCommitterCorrupted(cview : View.committer, pt1 : port, pt2: port, pt1_corrupted : bool, pt2_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim, commit_msg_status : bool, vview : View.verifier) {
    var new_cview : View.committer;
    match message with
    | I2S.corrupt_committer_ack(b) => {
        new_cview <- cview ++ [View.C_env_b b];
        send Real.Adv.Pt1.send_view(Some cview)
	and transition WaitOpenCommitter_Corrupted(new_cview, pt1, pt2, pt1_corrupted, sim_crs, Some b, c_vals, vview). (* Adversary never forwards the commitment message, allow adversary to choose the message *)
    }
    | * => { fail. }
    end
  }

  state WaitOpen_IFAckVerifierCorrupted(cview : View.committer, pt1 : port, pt2: port, pt1_corrupted : bool, pt2_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim, commit_msg_status : bool, vview : View.verifier) {
    match message with
    | I2S.corrupt_verifier_ack => {
        send Real.Adv.Pt2.send_view(Some vview)
	and transition WaitOpen(cview, pt1, pt2, pt1_corrupted, pt2_corrupted, sim_crs, c_vals, o_vals_sim, commit_msg_status, vview).
    }
    | * => { fail. }
    end
  }

  state WaitFwd2Ok(cview : View.committer, pt1 : port, pt2: port, pt1_corrupted : bool, pt2_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim, o_rfake : Types.open_rfake, commit_msg_status : bool, vview : View.verifier, opened_bit : bool) {
    var crs : Cfptp.fkey * Pke.pkey;
    var pt1_corrupted' : bool;
    var fk : Cfptp.fkey; var bk : Cfptp.bkey; var pk : Pke.pkey; var sk : Pke.skey; (* Simulated CRS *)
    var x0, x1 : Cfptp.D; var r0, r1 : Pke.rand; (* Open msg values *)
    var o_vals : Types.open_vals;
    var new_vview : View.verifier;
    match message with
    | Real.Fwd2.FwAdv.fw_ok => {
        (* Instead of immediately sending "open_ok" to ideal functionality, first simulate the verifier's CRS request message, which is seen by the adversary. *)
	(fk, bk, pk, sk) <- sim_crs;
        crs <- (fk, pk);
	(x0, x1, r0, r1) <- o_vals_sim;
	o_vals <- ((opened_bit ? x1 : x0), (opened_bit ? r1 : r0));
	new_vview <- vview ++ [View.V_omsg o_vals];
        send Real.Crs.Adv.crs_send_req(intport Real.Verifier, crs)
	and transition WaitVerifierCrsOk(pt2_corrupted, crs, new_vview).
    }
    | Real.Adv.Pt1.corrupt => { (* Adversary corrupts the committer *)
        pt1_corrupted' <- true;
      	send I2S.corrupt_committer
	and transition WaitFwd2Ok_IFAckCommitterCorrupted(cview, pt1, pt2, sim_crs, c_vals, o_vals_sim, commit_msg_status, vview).
      }
    | * => { fail. }
    end
  }

  state WaitFwd2Ok_IFAckCommitterCorrupted(cview : View.committer, pt1 : port, pt2: port, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, o_vals_sim : Types.open_vals_sim, commit_msg_status : bool, vview : View.verifier) {
    var new_cview : View.committer;
    match message with
    | I2S.corrupt_committer_ack(b) => {
        new_cview <- cview ++ [View.C_env_b b];
        send Real.Adv.Pt1.send_view(Some cview)
	and transition WaitAdvOpen( pt1, pt2, sim_crs, Some b, c_vals, vview). (* Adversary never forwards the open message, allow adversary to choose the message *)
    }
    | * => { fail. }
    end
  }


  (* --- --- --- --- --- ---  *)
  (* States for when the committer is CORRUPTED *)
  (* --- --- --- --- --- ---  *)

  state WaitCrsOkCommitter_Corrupted(cview : View.committer, pt1: port, pt2 : port, pt1_corrupted : bool, sim_crs : Types.sim_crs, committed_b : bool) {
    match message with
    | Real.Crs.Adv.crs_send_ok => {
      (* Give the adversary the CRS string and ask it to generate the corrupted commit message *)
      send Real.Adv.Pt1.commit_msg_req(cview)
      and transition WaitAdvCommit(cview, pt1, pt2, pt1_corrupted, sim_crs, committed_b).
    }
    | * => { fail. }
    end
  }

  state WaitAdvCommit(cview : View.committer, pt1: port, pt2: port, pt1_corrupted : bool, sim_crs : Types.sim_crs, committed_b : bool) {
    var commit_msg_status : bool;
    var c_vals : Types.commit_vals;
    var vview : View.verifier;
    match message with
    | Real.Adv.Pt1.commit_msg_rsp(y', c_false', c_true') => {
        commit_msg_status <- false; (* Record that a CORRUPTED commitment message was sent *)
	c_vals <- (y', c_false', c_true');
	vview <- [View.V_c_env_port pt1; View.V_v_env_port pt2; View.V_cmsg c_vals];
        send Real.Fwd1.FwAdv.fw_obs
	    (intport Real.Committer, (* Sender is the Committer *)
	     intport Real.Verifier,   (* Receiver is the Verifier *)
	     ForwardingEncodings.epdp_commit_univ.`enc
	     (pt1, pt2, y', c_false', c_true'))
        and transition WaitFwd1OkCommitter_Corrupted(cview, pt1, pt2, pt1_corrupted, sim_crs, c_vals, committed_b, commit_msg_status, vview).
      }
    | * => { fail. }
    end
  }

  state WaitFwd1OkCommitter_Corrupted(cview : View.committer, pt1: port, pt2: port, pt1_corrupted : bool, sim_crs : Types.sim_crs, c_vals : Types.commit_vals, committed_b : bool, commit_msg_status : bool, vview : View.verifier) {
    (* var x0, x1 : Pke.plaintext; *)
    (* var x0_back, x1_back : Cfptp.D; *)
    var x' : Pke.plaintext;
    var y : Cfptp.D;
    var b' : bool;
    var fk : Cfptp.fkey; var bk : Cfptp.bkey; var pk : Pke.pkey; var sk : Pke.skey; (* Simulated CRS *)
    var y' : Cfptp.D; var c_false', c_true' : Pke.ciphertext; (* Commit msg *)
    match message with
    | Real.Fwd1.FwAdv.fw_ok => { (* i.e. corrupted commit message was sent *)
        (fk, bk, pk, sk) <- sim_crs;
	(y', c_false', c_true') <- c_vals;
        (* Recover x' *)
	x' <- Pke.dec sk c_false';

	if (commit_msg_status) {(* If the commit message was sent honestly *)
	  (* previously committed bit *)
	  b' <- committed_b;
	  send I2S.commit_ok(Some b') (* The adversary committed to b' *)
	  and transition WaitOpenCommitter_Corrupted(cview, pt1, pt2, pt1_corrupted, sim_crs, Some false, c_vals, vview).
	}
	else { (* commit message was not sent honestly *)
	  y <- Cfptp.forw fk x' false;
	  b' <- true;
	  if (y' = y) {
	     b' <- false;
	  } (* else b' = 1 by default *)
	  send I2S.commit_ok(Some b') (* The adversary committed to b' *)
	  and transition WaitOpenCommitter_Corrupted(cview, pt1, pt2, pt1_corrupted, sim_crs, Some b', c_vals, vview).
	}


	(*
        (* Decrypt c0, c1 to compute x0, x1 *)
	x0 <- Pke.dec sk c_false';
	x1 <- Pke.dec sk c_true';
	(* Invert y' w.r.t. cfptp *)
	x0_back <- Cfptp.back bk y' false;
	x1_back <- Cfptp.back bk y' true;

	if (x0 = x0_back) {
	  send I2S.commit_ok(Some false) (* The adversary committed to b = false *)
	  and transition WaitOpenCommitter_Corrupted(pt1, pt2, pt1_corrupted, sim_crs, Some false, y', c_false', c_true').
	}
	elif (x1 = x1_back) {
	  send I2S.commit_ok(Some true) (* The adversary committed to b = true *)
	  and transition WaitOpenCommitter_Corrupted(pt1, pt2, pt1_corrupted, sim_crs, Some true, y', c_false', c_true').
	}
	else {
	  send I2S.commit_ok(None) (* The adversary sent a message that doesn't correspond to committing either 0 or 1 *)
	  and transition WaitOpenCommitter_Corrupted(pt1, pt2, pt1_corrupted, sim_crs, None, y', c_false', c_true').
	}
	*)
    }
    | * => { fail. }
    end
  }

  state WaitOpenCommitter_Corrupted(cview : View.committer, pt1: port, pt2: port, pt1_corrupted : bool, sim_crs : Types.sim_crs, committed_b : bool option, c_vals : Types.commit_vals, vview : View.verifier) {
    match message with
    | I2S.open_req(b') => {
        (* Ask adversary for the committer's open message *)
        send Real.Adv.Pt1.open_msg_req
	and transition WaitAdvOpen(pt1, pt2, sim_crs, committed_b, c_vals, vview).
    }
    | * => { fail. }
    end
  }

  state WaitAdvOpen(pt1 : port, pt2 : port, sim_crs : Types.sim_crs, committed_b : bool option, c_vals : Types.commit_vals, vview : View.verifier) {
    var o_vals : Types.open_vals;
    var o_rfake : Types.open_rfake;
    match message with
    | Real.Adv.Pt1.open_msg_rsp(b', x', r_b', r_nb') => {
        match committed_b with
	| Some ext_b => {
	    if (ext_b <> b') { fail. }
	    else {
	      o_vals <- (x', r_b');
	      o_rfake <- r_nb';
	      send Real.Fwd2.FwAdv.fw_obs
              (intport Real.Committer, (* Sender is the Committer *)
	       intport Real.Verifier,   (* Recevier is the Verifier *)
	       ForwardingEncodings.epdp_open_univ.`enc
	       (b', x', r_b', r_nb'))
      	      and transition WaitFwd2OkCommitter_Corrupted(pt1, pt2, sim_crs, committed_b, c_vals, b', o_vals, o_rfake, vview).
	    }
	}
	| None => { fail. }
	end
	(*
        send Real.Fwd2.FwAdv.fw_obs
        (intport Real.Committer, (* Sender is the Committer *)
	 intport Real.Verifier,   (* Recevier is the Verifier *)
	 ForwardingEncodings.epdp_open_univ.`enc
	 (b', x', r' ))
      	and transition WaitFwd2OkCommitter_Corrupted(pt1, pt2, fk, bk, pk, committed_b, y', c_false', c_true', b', x', r').
	*)
      }
    | * => { fail. }
    end
  }

  state WaitFwd2OkCommitter_Corrupted(pt1 : port, pt2 : port, sim_crs : Types.sim_crs, committed_b : bool option, c_vals : Types.commit_vals, b' : bool, o_vals : Types.open_vals, o_rfake : Types.open_rfake, vview : View.verifier) {
    var x : Cfptp.D;
    var ct : Pke.ciphertext;
    var crs : Cfptp.fkey * Pke.pkey;
    var fk : Cfptp.fkey; var bk : Cfptp.bkey; var pk : Pke.pkey; var sk : Pke.skey; (* Simulated CRS *)
    var y' : Cfptp.D; var c_false', c_true' : Pke.ciphertext; (* Commit msg *)
    var x' : Cfptp.D; var r' : Pke.rand; (* Open values *)
    var new_vview : View.verifier;
    match message with
    | Real.Fwd2.FwAdv.fw_ok => {
        (fk, bk, pk, sk) <- sim_crs;
	(y', c_false', c_true') <- c_vals;
	(x', r') <- o_vals;

        x <- Cfptp.back bk y' b';
	ct <- Pke.enc pk x r';
	crs <- (fk, pk);

	new_vview <- vview ++ [View.V_omsg_b b'; View.V_omsg o_vals; View.V_omsg_rfake o_rfake];
	if (x = x' /\ (b' ? c_true' : c_false') = ct) {
	  match committed_b with
	  | Some b => {
	      if (b' = b) {
	        send Real.Crs.Adv.crs_send_req(intport Real.Verifier, crs)
	     	and transition WaitVerifierCrsOk(false, crs, new_vview).
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

  state WaitVerifierCrsOk(pt2_corrupted : bool, crs : Types.crs, vview : View.verifier) { (* Emulate the verifier's call to the CRS ideal functionality *)
    var new_vview : View.verifier;
    match message with
    | Real.Crs.Adv.crs_send_ok => {
        new_vview <- vview ++ [View.V_crs crs];
        send I2S.open_ok (* Tells ideal functionality that Forwarder OKs the open message. *) (* TODO: forward V's view to adversary, delay I2S.open_ok *)
	and transition Final.
    }
    | Real.Adv.Pt2.corrupt => { (* Adversary can corrupt when control returns to environment (and prior to receiving open_req *)
	send I2S.corrupt_verifier
	and transition WaitVerifierCrsOk_IFAckVerifierCorrupted(true, crs, vview).
      }
    | * => { fail. }
    end
  }

  state WaitVerifierCrsOk_IFAckVerifierCorrupted(pt2_corrupted : bool, crs : Types.crs, vview : View.verifier) {
    match message with
    | I2S.corrupt_verifier_ack => {
        send Real.Adv.Pt2.send_view(Some vview)
	and transition WaitVerifierCrsOk(pt2_corrupted, crs, vview).
    }
    | * => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }

  (* TODO: what is the correct behavior if both pt1 and pt2 are corrupted? *)
  (* TODO: Forward the verifier's state to the adversary every time the verifier receives a message. *)
  (* TODO: Double check simulation: make sure generating real values for both b=0,1, later after learning b's value, oblviously sammple 1-b's randomness (03-23). *)
}
