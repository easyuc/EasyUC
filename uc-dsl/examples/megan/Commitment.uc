(* Commitment.uc *)

(* This code models a two party UC Commitment scheme. It simplifies the scheme of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf) to only allow static corruption of the committer. This is a unit containing an ideal functionality, a real functionality (i.e. real protocol description), and a simulator. *)

(* Author: Megan Chen *)

(* Import required .uc files *)
uc_requires Forwarding Crs.

(* Import required easycrypt files. *)
ec_requires Cfptp Pke Encodings View.

(* Direct interfaces, which are between ideal functionality and environment, from ideal functionality's perspective. Note that the ideal functionality emulates parties. *)
direct DirPt1 {  (* Party 1, i.e. the Committer *)
  in pt1@commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment of a value u to pt2 *)

  in pt1@open_req  (* message to pt2, asking to send the opening of the commitment to pt2 *)

  (* Corruption status messages *)
  in pt1@committer_corrupted_req (* pt1 asks whether Committer is corrupted *)

  out committer_corrupted_rsp( corrupted : bool )@pt1 (* tells pt1 whether it is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *)
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

  in committer_corrupted_rsp(pt1_corrupted : bool) (* Receive from simulator whether each port pt is corrupted. True = corrupted. False = honest. *)

  out committer_bit(u : bool option) (* If pt1 is corrupted, send its boolean input u to the simulator. Otherwise, send None. Note that pt2 has no input. *)

  in commit_ok(u' : bool option) (* Simulator OKs sending a commit message to pt2. It also has the option of detecting u' and returning it. *)

  (* Open Phase *)
  out open_req(b' : bool) (* open message request from ideal functionality to simulator. If it knows the bit b' to be opened, return it. *)

  in open_ok (* simulator OKs sending a open message to pt2, conveying no additional information. Otherwise, send None. *)

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
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( false )@pt1 (* send pt1's corruption status *)
  	and transition WaitCommitReq. (* return to this same state *)
      }
    | * => { fail. }
    end
  }

  state WaitCorruptions(b : bool, pt1 : port, pt2 : port) {
    match message with
    (* Simulator responds to ideal functionality saying whether pt1 is corrupted *)
    | I2S.committer_corrupted_rsp(pt1_corrupted) => {
        send I2S.committer_bit( pt1_corrupted ? (Some b) : (None) ) (* If pt1 is corrupted, send its input to the simulator. Otherwise send None. *)
        and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted). (* Transition to whether Sim OKs pt1's commit request *)
      }
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( false )@pt1 (* send pt1's corruption status *)
  	and transition WaitCorruptions(b, pt1, pt2). (* return to this same state *)
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
        send Dir.Pt2.commit_rsp(pt1)@pt2  (* Deliver pt1's commitment message to pt2, which excludes the commited value u *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, b').   (* Transition to waiting for pt1's open message *)
      }
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted). (* return to this same state *)
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
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, b'). (* return to this same state *)
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
	      send Dir.Pt2.open_rsp(b')@pt2
	      and transition Final(pt1_corrupted).
	    }
	  | None => { (* Note: If committer is corrupted and the ideal functionality receives b' = None from the simulator in the commit round, the simulator will never send open_ok, so the following message won't occur. *)
	      send Dir.Pt2.open_rsp(b)@pt2
	      and transition Final(pt1_corrupted).
	    }
	  end
      }
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, b'). (* return to this same state *)
      }
    | * => { fail. }
    end
  }

  state Final(pt1_corrupted : bool) {
    match message with
    | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
        send Dir.Pt1.committer_corrupted_rsp( pt1_corrupted )@pt1 (* send pt1's corruption status *)
	and transition Final(pt1_corrupted). (* return to this same state *)
      }
    | * => { fail. }
    end
  }
}

(* Adversarial interfaces between a real party and the adversary, from the perspective of the real party *)
adversarial Pt1Adv {

  (* Initial corruption sequence *)
  out committer_corrupted_req (* Ask adversary if the committer is corrupted *)

  in committer_corrupted_rsp( corrupted : bool ) (* corrupted = true if corrupted. corrupted = false if the party is honest *)

  out committer_view(opt : (View.committer) option) (* sends None if committer is not corrupted. Sends all known data if committer is corrupted.*)

  in continue (* Adv response message that returns control to committer *)

  (* Adversary corruptions later than initial *)
  in corrupt (* adversary tells Pt1 it is corrupted *)

  out send_view (view : View.committer) (* send the committer's view thus far to the adversary *)

  (* Post-corruption messages with the adversary *)
  out commit_msg_req(view: View.committer) (* Forward updated view (including CRS to the adversary *)

  in commit_msg_rsp(y': Cfptp.D, c_b': Pke.ciphertext, c_nb': Pke.ciphertext) (* Adv responds with the y, c_b, c_bn values it wants to send to the verifier *)

  out open_msg_req (* Ask adv for the open message *)

  in open_msg_rsp(b' : bool, x' : Cfptp.D, r_bool' : Pke.rand)
}

adversarial Pt2Adv {

  (* Initial corruption sequence *)
  out verifier_corrupted_req (* Ask adversary if the verifier is corrupted *)

  in verifier_corrupted_rsp( corrupted : bool ) (* corrupted = true if corrupted. corrupted = false if the party is honest *)

  (* Adversary corruptions later than initial *)
  in corrupt (* adversary tells Pt1 it is corrupted *)

  out send_state (view : View.verifier) (* send the committer's view thus far to the adversary *)
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
      var view : View.committer;
      match message with
      | pt1@Dir.Pt1.commit_req(pt2, b) => {
      	  view <- []; (* initialize list *)
	  view <- view ++ [View.C_c_env_port pt1; View.C_v_env_port pt2; View.C_env_b b];
	  send Adv.Pt1.committer_corrupted_req (* Ask adversary about committer's corruption status *)
	  and transition WaitCorruptionStatus(view, pt1, pt2, b).
	}
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( false )@pt1 (* send pt1's corruption status *)
  	  and transition WaitCommReq. (* return to this same state *)
        }
      | * => { fail. }
      end
    }

    state WaitCorruptionStatus(view : View.committer, pt1 : port, pt2 : port, b : bool) {
      var new_view : View.committer;
      match message with
      | Adv.Pt1.committer_corrupted_rsp( corrupted ) => {
          new_view <- view ++ [View.C_corrupted corrupted];
          send Adv.Pt1.committer_view( corrupted ? Some(new_view) : None)
	  and transition WaitContinue(new_view, pt1, pt2, b, corrupted).
	}
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( false )@pt1 (* send pt1's corruption status *)
  	  and transition WaitCorruptionStatus(view, pt1, pt2, b). (* return to this same state *)
      }
      | * => { fail. }
      end
    }

    state WaitContinue(view : View.committer, pt1 : port, pt2 : port, b: bool, corrupted : bool) {
      (*var new_view : View.committer;*)
      match message with
      | Adv.Pt1.continue => {
      	  if (corrupted) {
	    send Crs.Pt.crs_req (* request CRS *)
	    and transition WaitCrs_Corrupted(view, pt1, pt2, b, corrupted). (* Go to states modelling corrupted committer *)
	  }
	  else { (* Committer honest *)
	    send Crs.Pt.crs_req (* request CRS *)
	    and transition WaitCrs(view, pt1, pt2, b, corrupted). (* Go to states modelling honest committer *)
	  }
	}
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitContinue(view, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | Adv.Pt1.corrupt => {
      	  send Adv.Pt1.send_view(view)
	  and transition WaitContinue(view, pt1, pt2, b, corrupted).
        }
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the committer is HONEST *)
    (* --- --- --- --- --- ---  *)
    state WaitCrs(view: View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      var new_view : View.committer;
      var x : Cfptp.D;
      var r_false, r_true : Pke.rand;
      var y : Cfptp.D;
      var c_b, c_nb : Pke.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)

	  (* generate commit message *)
	  x <$ Pke.dplaintext;
	  r_false <$ Pke.drand;
	  r_true <$ Pke.drand;

	  y <- Cfptp.forw fk x b; (* compute f_b(x), where f_b is a cfptp. *)
	  c_b <- Pke.enc pk x (b ? r_true : r_false); (* ciphertext c_b. Encrypt x using r_true if b = true, r_false if b = false *)
	  c_nb <- Pke.oblivenc pk (b ? r_false : r_true); (* ciphertext c_{1-b}. Obliviously encrypt to generate a ciphertext using randomness r_false if b = true, r_true if b = false *)

	  (* Add everything to the committer's view *)
	  new_view <- view ++ [View.C_crs_fk fk; View.C_crs_pk pk] (* CRS *)
	  	      	   ++ [View.C_cmsg_x x; View.C_cmsg_rfalse r_false; View.C_cmsg_rtrue r_true]
			   ++ [View.C_cmsg_y y; View.C_cmsg_cb c_b; View.C_cmsg_cnb c_nb];
	  (* send commit message to verifier *)
	  send Fwd1.D.fw_req
	       (intport Verifier, (* Send this to Verifier *)
	        Encodings.epdp_commit_univ.`enc
	        ( b ? (pt1, pt2, y, c_nb, c_b) : (pt1, pt2, y, c_b, c_nb) )
	       )
	  and transition WaitOpenReq(new_view, pt1, pt2, b, corrupted, x, b ? r_true : r_false).
	}
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitCrs(view, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitOpenReq(view : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool, x : Cfptp.D, r_bool : Pke.rand) {
      var new_view : View.committer;
      match message with
      | pt1'@Dir.Pt1.open_req => {
      	  if (pt1 = pt1') {
	    new_view <- view ++ [View.C_open_c_env_port pt1'];
	    send Fwd2.D.fw_req
	       (intport Verifier,
	       Encodings.epdp_open_univ.`enc
	       (b, x, r_bool))
            and transition Final(new_view, corrupted).
	  } else { fail. }
        }
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitOpenReq(view, pt1, pt2, b, corrupted, x, r_bool). (* return to this same state *)
   	}
      | Adv.Pt1.corrupt => { (* TODO: technically Env can corrupt here right? *)
      	  send Adv.Pt1.send_view(view)
	  and transition WaitOpenReq_Corrupted(view, pt1, pt2, b, corrupted).
        }
      | * => { fail. }
      end
    }

    (* --- --- --- --- --- ---  *)
    (* States for when the committer is CORRUPTED *)
    (* --- --- --- --- --- ---  *)
    state WaitCrs_Corrupted(view : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      var new_view : View.committer;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse CRS *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)
	  new_view <- view ++ [View.C_crs_fk fk; View.C_crs_pk pk];
	  (* Ask the adversary for y, c_false, c_true *)
	  send Adv.Pt1.commit_msg_req(new_view)
	  and transition WaitAdvCommit(new_view, pt1, pt2, b, corrupted).
	}
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitCrs_Corrupted(view, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitAdvCommit(view: View.committer, pt1 : port, pt2 : port, b : bool, corrupted: bool) {
      match message with
      | Adv.Pt1.commit_msg_rsp(y', c_false', c_true') => {
          send Fwd1.D.fw_req
	       (intport Verifier,
	       Encodings.epdp_commit_univ.`enc
	       (pt1, pt2, y', c_false', c_true'))
	  and transition WaitOpenReq_Corrupted(view, pt1, pt2, b, corrupted).
      }
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitAdvCommit(view, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitOpenReq_Corrupted(view : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      match message with
      | pt1@Dir.Pt1.open_req => {
      	  (* Ask the adversary for b, x, r_bool *)
	  send Adv.Pt1.open_msg_req
	  and transition WaitAdvOpen(view, pt1, pt2, b, corrupted).
        }
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitOpenReq_Corrupted(view, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state WaitAdvOpen(view : View.committer, pt1 : port, pt2 : port, b : bool, corrupted : bool) {
      match message with
      | Adv.Pt1.open_msg_rsp(b', x', r_bool') => {
      	  send Fwd2.D.fw_req
	       (intport Verifier,
	       Encodings.epdp_open_univ.`enc
	       (b', x', r_bool'))
          and transition Final(view, corrupted).
        }
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition WaitAdvOpen(view, pt1, pt2, b, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }

    state Final(view: View.committer, corrupted : bool) {
      match message with
      | pt1@Dir.Pt1.committer_corrupted_req => { (* pt1 asks if it is corrupted *)
          send Dir.Pt1.committer_corrupted_rsp( corrupted )@pt1 (* send pt1's corruption status *)
	  and transition Final(view, corrupted). (* return to this same state *)
   	}
      | * => { fail. }
      end
    }
  }

  party Verifier serves Dir.Pt2 Adv.Pt2 {

    initial state WaitCommit {
      var view : View.verifier;
      var pt1, pt2 : port;
      var y : Cfptp.D;
      var c_false, c_true : Pke.ciphertext;
      match message with
      | Fwd1.D.fw_rsp(_, u) => { (* Verifier is activated after receiving a commit message *)
          match Encodings.epdp_commit_univ.`dec u with
          | Some tr => {
              (pt1, pt2, y, c_false, c_true) <- tr;
	      view <- [View.V_c_env_port pt1; View.V_v_env_port pt2]
	      	      ++ [View.V_cmsg_y y; View.V_cmsg_cfalse c_false; View.V_cmsg_ctrue c_true];
              send Adv.Pt2.verifier_corrupted_req
	      and transition WaitCorruptionStatus(view, pt1, pt2, y, c_false, c_true).
            }
          | None => { fail. }  (* cannot happen *)
          end
        }
      | * => { fail. }
      end
    }

    state WaitCorruptionStatus(view : View.verifier, pt1 : port, pt2 : port, y : Cfptp.D, c_false : Pke.ciphertext, c_true : Pke.ciphertext) {
      var new_view : View.verifier;
      match message with
      | Adv.Pt2.verifier_corrupted_rsp( corrupted ) => { (* After receiving corruption status, do nothing (update later to allow V to send arbitrary messages to C *)
      	  new_view <- view ++ [View.V_corrupted corrupted];
          send Dir.Pt2.commit_rsp(pt1)@pt2
	  and transition WaitOpen(new_view, pt1, pt2, y, c_false, c_true, corrupted).
	}
      | * => { fail. }
      end
    }

    state WaitOpen(view : View.verifier, pt1 : port, pt2 : port, y : Cfptp.D, c_false : Pke.ciphertext, c_true : Pke.ciphertext, corrupted : bool) {
      var new_view : View.verifier;
      var b : bool;
      var x : Cfptp.D;
      var r_bool : Pke.rand;
      match message with
      | Fwd2.D.fw_rsp(_, u) => {
          match Encodings.epdp_open_univ.`dec u with
          | Some tr => {
              (b, x, r_bool) <- tr;
	      new_view <- view ++ [View.V_omsg_b b; View.V_omsg_x x; View.V_omsg_rbool r_bool];
              send Crs.Pt.crs_req
	      and transition WaitCrs(new_view, pt1, pt2, y, c_false, c_true, corrupted, b, x, r_bool).
            }
          | None => { fail. }  (* cannot happen *)
          end
        }
      | * => { fail. }
      end
    }

    state WaitCrs(view : View.verifier, pt1 : port, pt2 : port, y : Cfptp.D, c_false : Pke.ciphertext, c_true : Pke.ciphertext, corrupted: bool, b : bool, x : Cfptp.D, r_bool : Pke.rand) {
      var new_view : View.verifier;
      var y' : Cfptp.D;
      var c' : Pke.ciphertext;
      var fk : Cfptp.fkey;
      var pk : Pke.pkey;
      match message with
      | Crs.Pt.crs_rsp(crs) => {
      	  (* parse crs *)
	  (fk, pk) <- crs; (* fk is forward key for Cfptp. pk is public key for public key encryption *)
	  new_view <- view ++ [View.V_crs_fk fk; View.V_crs_pk pk];
	  (* Do verification checks *)
	  y' <- Cfptp.forw fk x b;
	  c' <- Pke.enc pk x r_bool;

	  if (y' = y /\ (b ? (c' = c_true) : (c' = c_false) )) {
	    send Dir.Pt2.open_rsp(b)@pt2
	    and transition Final(new_view).
	  }
	  else { fail. }
        }
      | * => { fail. }
      end
    }

    state Final(view : View.verifier) {
      match message with
      | * => { fail. }
      end
    }
  }

}

(* Simulator *)
simulator Sim uses I2S simulates Real {

  initial state WaitCommitReq {
    var view : View.committer;
    match message with
    | I2S.commit_req(pt1, pt2) => { (* Committer asks commitment request *)
        view <- [] ++ [View.C_c_env_port pt1; View.C_v_env_port pt2];
        send Real.Adv.Pt1.committer_corrupted_req  (* Ask adversary if Committer is corrupted *)
	and transition WaitCommitterCorruption(view, pt1, pt2). (* Wait to see if committer is corrupted *)
      }
    | * => { fail. }
    end
  }

  state WaitCommitterCorruption(view : View.committer, pt1 : port, pt2 : port) {
    var new_view : View.committer;
    match message with
    | Real.Adv.Pt1.committer_corrupted_rsp( pt1_corrupted ) => {
        new_view <- view ++ [View.C_corrupted pt1_corrupted];
	send I2S.committer_corrupted_rsp(pt1_corrupted)
	and transition WaitIFCommitterCorruptMsg(new_view, pt1, pt2, pt1_corrupted).

      }
    | * => { fail. }
    end
  }

  state WaitIFCommitterCorruptMsg(view : View.committer, pt1 : port, pt2 : port, pt1_corrupted : bool) {
    var new_view : View.committer;
    match message with
    | I2S.committer_bit(u) => {
	match u with
	| Some b => { (* Receive corrupted committer's bit b *)
	    new_view <- view ++ [View.C_env_b b];
	    send Real.Adv.Pt1.committer_view(Some new_view) (* Forward data to adversary *)
	    and transition WaitContinue(new_view, pt1, pt2, pt1_corrupted).
	  }
	| None => { (* For an honest committer, forward None to the adversary *)
	    send Real.Adv.Pt1.committer_view(None)
	    and transition WaitContinue(view, pt1, pt2, pt1_corrupted).
	  }
    	end
    }
    | * => { fail. }
    end
  }

  state WaitContinue(view : View.committer, pt1: port, pt2: port, pt1_corrupted : bool) {
    var fk : Cfptp.fkey;
    var bk : Cfptp.bkey;
    var pk : Pke.pkey;
    var sk : Pke.skey;
    var crs : Cfptp.fkey * Pke.pkey;
    var new_view : View.committer;
    match message with
    | Real.Adv.Pt1.continue => {
        (* Simulate the CRS ideal functionality *)
        (fk, bk) <$ Cfptp.keygen;
        (pk, sk) <$ Pke.dkeygen;
	crs <- (fk, pk);
	new_view <- view ++ [View.C_crs_fk fk; View.C_crs_pk pk];
	if (pt1_corrupted) {
	  send Real.Crs.I2S.crs_send_req(intport Real.Committer, crs) (* Ask adversary to send crs to the Committer *)
	  and transition WaitCrsOkCommitterCorrupted(new_view, pt1, pt2, pt1_corrupted, fk, bk, pk, sk).
	}
	else {
	  send Real.Crs.I2S.crs_send_req(intport Real.Committer, crs) (* Ask adversary to send crs to the Committer *)
	  and transition WaitCrsOk(pt1, pt2, pt1_corrupted, fk, bk, pk, sk).
	}
    }
    | * => { fail. }
    end
  }

  (* --- --- --- --- --- ---  *)
  (* States for when the committer is HONEST *)
  (* --- --- --- --- --- ---  *)

  state WaitCrsOk(pt1: port, pt2 : port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, sk : Pke.skey) {
    var y, x0, x1 : Cfptp.D;
    var r0, r1 : Pke.rand;
    var c0, c1 : Pke.ciphertext;
    var new_view : View.committer;
    match message with
    | Real.Crs.I2S.crs_send_ok => {
      y <$ Cfptp.dD;
      x0 <- Cfptp.back bk y false;
      x1 <- Cfptp.back bk y true;
      r0 <$ Pke.drand;
      r1 <$ Pke.drand;
      c0 <- Pke.enc pk x0 r0;
      c1 <- Pke.oblivenc pk r1;

      (* send (pt1, pt2, y, c0, c1) to the adversary, who OKs forwarding to the verifier *)
      send Real.Fwd1.FwAdv.fw_obs
      	   (intport Real.Committer, (* Sender is the Committer *)
	    intport Real.Verifier,   (* Receiver is the Verifier *)
	    Encodings.epdp_commit_univ.`enc
	    (pt1, pt2, y, c0, c1))
      and transition WaitFwd1Ok(pt1, pt2, fk, pk, x0, x1, r0, r1). (* Only remember the state arguments required for open stage. *)
    }
    | * => { fail. }
    end
  }

  state WaitFwd1Ok(pt1 : port, pt2: port, fk : Cfptp.fkey, pk : Pke.pkey, x0 : Cfptp.D, x1 : Cfptp.D, r0 : Pke.rand, r1 : Pke.rand) {
    match message with
    | Real.Fwd1.FwAdv.fw_ok => {
      send I2S.commit_ok(None) (* Tells ideal functionality commit message is OK'd by Forwarder. *)
      and transition WaitOpen(pt1, pt2, fk, pk, x0, x1, r0, r1).
    }
    | * => { fail. }
    end
  }

  state WaitOpen(pt1 : port, pt2: port, fk : Cfptp.fkey, pk : Pke.pkey, x0 : Cfptp.D, x1 : Cfptp.D, r0 : Pke.rand, r1 : Pke.rand) {
    var b : bool;
    match message with
    | I2S.open_req(b') => {
        (* send (b', xb, r_bool) to the adversary, who OKs forwarding to the verifier *)
        send Real.Fwd2.FwAdv.fw_obs
      	(intport Real.Committer, (* Sender is the Committer *)
	 intport Real.Verifier,   (* Recevier is the Verifier *)
	 Encodings.epdp_open_univ.`enc
	 (b', b' ? x1 : x0, b' ? r1 : r0))
      	and transition WaitFwd2Ok(pt1, pt2, fk, pk).
    }
    | * => { fail. }
    end
  }

  state WaitFwd2Ok(pt1 : port, pt2: port, fk : Cfptp.fkey, pk : Pke.pkey) {
    var crs : Cfptp.fkey * Pke.pkey;
    match message with
    | Real.Fwd2.FwAdv.fw_ok => {
        crs <- (fk, pk);
        send Real.Crs.I2S.crs_send_req(intport Real.Verifier, crs)
	and transition WaitVerifierCrsOk.
    }
    | * => { fail. }
    end
  }


  (* --- --- --- --- --- ---  *)
  (* States for when the committer is CORRUPTED *)
  (* --- --- --- --- --- ---  *)

  state WaitCrsOkCommitterCorrupted(view : View.committer, pt1: port, pt2 : port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, sk : Pke.skey) {
    match message with
    | Real.Crs.I2S.crs_send_ok => {
      (* Give the adversary the CRS string and ask it to generate the corrupted commit message *)
      send Real.Adv.Pt1.commit_msg_req(view)
      and transition WaitAdvCommit(pt1, pt2, pt1_corrupted, fk, bk, pk, sk).
    }
    | * => { fail. }
    end
  }

  state WaitAdvCommit(pt1: port, pt2: port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, sk : Pke.skey) {
    match message with
    | Real.Adv.Pt1.commit_msg_rsp(y', c_false', c_true') => {

        send Real.Fwd1.FwAdv.fw_obs
	    (intport Real.Committer, (* Sender is the Committer *)
	     intport Real.Verifier,   (* Receiver is the Verifier *)
	     Encodings.epdp_commit_univ.`enc
	     (pt1, pt2, y', c_false', c_true'))
        and transition WaitFwd1OkCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, y', c_false', c_true').
      }
    | * => { fail. }
    end
  }

  state WaitFwd1OkCommitterCorrupted(pt1: port, pt2: port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, sk : Pke.skey, y' : Cfptp.D, c_false' : Pke.ciphertext, c_true' : Pke.ciphertext) {
    var x0, x1 : Pke.plaintext;
    var x0_back, x1_back : Cfptp.D;
    match message with
    | Real.Fwd1.FwAdv.fw_ok => {
        (* Decrypt c0, c1 to compute x0, x1 *)
	x0 <- Pke.dec sk c_false';
	x1 <- Pke.dec sk c_true';
	(* Invert y' w.r.t. cfptp *)
	x0_back <- Cfptp.back bk y' false;
	x1_back <- Cfptp.back bk y' true;
	if (x0 = x0_back) {
	  send I2S.commit_ok(Some false) (* The adversary committed to b = false *)
	  and transition WaitOpenCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, Some false, y', c_false', c_true').
	}
	elif (x1 = x1_back) {
	  send I2S.commit_ok(Some true) (* The adversary committed to b = true *)
	  and transition WaitOpenCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, Some true, y', c_false', c_true').
	}
	else {
	  send I2S.commit_ok(None) (* The adversary sent a message that doesn't correspond to committing either 0 or 1 *)
	  and transition WaitOpenCommitterCorrupted(pt1, pt2, pt1_corrupted, fk, bk, pk, sk, None, y', c_false', c_true').
	}
    }
    | * => { fail. }
    end
  }

  state WaitOpenCommitterCorrupted(pt1: port, pt2: port, pt1_corrupted : bool, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, sk : Pke.skey, committed_b : bool option, y' : Cfptp.D, c_false' : Pke.ciphertext, c_true' : Pke.ciphertext) {
    match message with
    | I2S.open_req(b') => {
        (* Ask adversary for the committer's open message *)
        send Real.Adv.Pt1.open_msg_req
	and transition WaitAdvOpen(pt1, pt2, fk, bk, pk, committed_b, y', c_false', c_true').
    }
    | * => { fail. }
    end
  }

  state WaitAdvOpen(pt1 : port, pt2 : port, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, committed_b : bool option, y' : Cfptp.D, c_false' : Pke.ciphertext, c_true' : Pke.ciphertext) {
    match message with
    | Real.Adv.Pt1.open_msg_rsp(b', x', r') => {
        send Real.Fwd2.FwAdv.fw_obs
        (intport Real.Committer, (* Sender is the Committer *)
	 intport Real.Verifier,   (* Recevier is the Verifier *)
	 Encodings.epdp_open_univ.`enc
	 (b', x', r' ))
      	and transition WaitFwd2OkCommitterCorrupted(pt1, pt2, fk, bk, pk, committed_b, y', c_false', c_true', b', x', r').
      }
    | * => { fail. }
    end
  }

  state WaitFwd2OkCommitterCorrupted(pt1 : port, pt2 : port, fk : Cfptp.fkey, bk : Cfptp.bkey, pk : Pke.pkey, committed_b : bool option, y' : Cfptp.D, c_false' : Pke.ciphertext, c_true' : Pke.ciphertext, b' : bool, x' : Cfptp.D, r' : Pke.rand) {
    var x : Cfptp.D;
    var ct : Pke.ciphertext;
    var crs : Cfptp.fkey * Pke.pkey;
    match message with
    | Real.Fwd2.FwAdv.fw_ok => {
        x <- Cfptp.back bk y' b';
	ct <- Pke.enc pk x r';
	crs <- (fk, pk);
	if (x = x' /\ (b' ? c_true' : c_false') = ct) {
	  match committed_b with
	  | Some b => {
	      if (b' = b) {
	        send Real.Crs.I2S.crs_send_req(intport Real.Verifier, crs)
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
    | Real.Crs.I2S.crs_send_ok => {
        send I2S.open_ok (* Tells ideal functionality that Forwarder OKs the open message. *)
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
