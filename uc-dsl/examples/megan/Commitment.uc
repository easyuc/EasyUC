(* Commitment.uc *)

(* This contains a two party UC F_com ideal functionality, as described in Figure 2 of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf). This is a unit only containing one ideal functionality, no real functionalities (i.e. real protocol descriptions) and no simulators, and no extraneous interfaces *)

(* Import required easycrypt files. *)
(* ec_requires +Commitment. *)

(* Direct interfaces, which are between ideal functionality and environment, from ideal functionality's perspective. Note that the ideal functionality emulates parties. *)
direct CommDirPt1 {  (* Party 1, i.e. the Committer *)
  in pt1@commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment of a value u to pt2 *)

  in pt1@open_req()  (* message to pt2, asking to send the opening of the commitment to pt2 *)

  (* Corruption status messages *)
  in corrupted (* Environment's backdoor query asking whether this party is corrupted *) (* Megan: this generates an error. How do I say that this message comes from the environment's port? *)

  out is_corrupted( is_corrupted : bool ) (* responds whether this party is corrupted, based on what the ideal functionality has recorded. is_corrupted = true if corrupted and false if not corrupted. *) (* How do I say that this message needs to be sent to the environment's port? *)
}

direct CommDirPt2 {  (* Party 2, i.e. the Receiver *)
  out commit_rsp(pt1 : port)@pt2  (* message to pt2, saying that pt1 has committed a message u *)

  out open_rsp(u : bool)@pt2  (* message to pt2, saying that pt1 sent u to it *)
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

  in sim_commit_rsp (* simulator OKs sending a commit message to pt2, conveying no additional information *)

  (* Open Phase *)
  out open_req (* open message request from ideal functionality to simulator, conveying no additional information *)

  in sim_open_rsp(u' : bool option) (* simulator OKs sending a open message to pt2, conveying no additional information. If the verifier is corrupted, it could send a new bit b' to pt2. Otherwise, send None. *)

}

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
        if (pt1_corrupted) {
          send CommI2S.pt1_corrupted_input(Some b) (* If pt1 is corrupted, send its input to the simulator *)
          and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted). (* Transition to whether Sim OKs pt1's commit request *)
        }
        else {
          send CommI2S.pt1_corrupted_input(None) (* If pt1 is not corrupted, send None to the simulator *)
	  and transition WaitCommitRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted). (* Transition to whether Sim OKs pt1's commit request *)
        }
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
    | CommI2S.sim_commit_rsp => {
        send CommDir.Pt2.commit_rsp(pt1)@pt2  (* Deliver pt1's commitment message to pt2, which excludes the commited value u *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, pt2_corrupted).   (* Transition to waiting for pt1's open message *)
      }
    | *                => { fail. }
    end
  }

  state WaitOpenReq(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool) {
    match message with
    (* Pt1 attempts to send an open message to pt2. Message is adversarially delayed, i.e. forwarded to Sim, who oks delivery. *)
    | pt1'@CommDir.Pt1.open_req => {
        if (pt1' = pt1) {
          send CommI2S.open_req  (* Ask simulator whether to deliver pt1's open message to pt2 *)
     	  and transition WaitOpenRsp(b, pt1, pt2, pt1_corrupted, pt2_corrupted). (* Transition to waiting for simulator's response *)
        }
        else {
          fail.
        }
      }
    | *                => { fail. }
    end
  }

  state WaitOpenRsp(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool) {
    match message with
    (* Simulator oks delivery of pt1's open message, which includes b, to pt2. *)
    | CommI2S.sim_open_rsp(b') => {
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
    | *                => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
