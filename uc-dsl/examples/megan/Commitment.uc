(* Commitment.uc *)

(* This contains a two party UC F_com ideal functionality, as described in Figure 2 of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf). This is a unit only containing one ideal functionality, no real functionalities (i.e. real protocol descriptions) and no simulators, and no extraneous interfaces *)

(* Import required easycrypt files. *)
ec_requires +Commitment.

(* Direct interfaces, which are between ideal functionality and environment, from ideal functionality's perspective *)
direct CommDirPt1 {  (* Party 1, i.e. the Committer *)
  in pt1@comm_party_init(b : bool) (* Give the committer sends its input bit to the ideal functionality *)

  in pt1@comm_commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment of a value u to pt2 *)

  in pt1@comm_open_req()  (* message to pt2, asking to send the opening of the commitment to pt2 *)
}

direct CommDirPt2 {  (* Party 2, i.e. the Receiver *)
  in pt2@comm_party_init() (* message initializing pt2 *)

  out comm_commit_rsp(pt1 : port)@pt2  (* message to pt2, saying that pt1 has committed a message u *)

  out comm_open_rsp(pt1 : port, u : bool)@pt2  (* message to pt2, saying that pt1 sent u to it *)
}

direct CommDir {
  Pt1 : CommDirPt1  (* Party 1 *)
  Pt2 : CommDirPt2  (* Party 2 *)
}

(* adversarial interface between ideal functionality and
   simulator, viewed from ideal functionality *)
adversarial CommI2S {

  (* *)
  (* Party 1's corruption interface *)
  (* *)

  out comm_pt1_init(pt1 : port) (* Committer (pt1)'s init message, which sends port address to simulator *)

  in comm_pt1_corrupted(pt1_corrupted : bool) (* Receive from simulator whether the committer port pt is corrupted. True = corrupted. False = honest. *)

  out comm_pt1_corrupted_input(u : party_input) (* If the committer is corrupted, send pt's boolean input u. Otherwise, send None *)
  

  (* *)
  (* Party 2's corruption interface *)
  (* *)

  out comm_pt2_init(pt2 : port) (* Receiver (pt2)'s init message, which sends port address to simulator *)

  in comm_pt2_corrupted(pt2_corrupted : bool) (* Receive from simulator whether the receiver port pt2 is corrupted *)
  
  out setup_done (* Tell simulator that the static corruption setup is done. Next comes the protocol. *)

  (* *)
  (* Commitment scheme interface *)
  (* *)

  out comm_sim_commit_req(pt1 : port, pt2 : port) (* commit message from ideal functionality to simulator,
    where pt1 is the committer and pt2 is the receiver *)

  in comm_sim_commit_rsp (* response from simulator to ideal functionality,
    conveying no additional information *)

  out comm_sim_open_req(u : bool) (* open message from ideal functionality to simulator,
    conveying no additional information *)

  in comm_sim_open_rsp (* response from simulator to ideal functionality,
    conveying no additional information *)

}

(* Ideal Functionality *)
functionality CommIdeal implements CommDir CommI2S {

  (* *)
  (* States for the static corruption interface *)
  (* *)

  initial state WaitPt1Init {
    match message with
    (* Get committer (pt1)'s input bit u from the environment *)
    | pt1@CommDir.Pt1.comm_party_init(b) => { 
        send CommI2S.comm_pt1_init(pt1) (* Send the committer (pt1)'s port address to the simulator *)
        and transition WaitPt1Corruption(b, pt1). (* Transition to waiting for simulator's decision to corrupt pt1 *)
      }
    | *                => { fail. }
    end
  }

  state WaitPt1Corruption(b : bool, pt1 : port) { 
    match message with
    (* Simulator responds to ideal functionality saying whether pt1 is corrupted *)
    | CommI2S.comm_pt1_corrupted(pt1_corrupted) => {
        if (pt1_corrupted) {
          send CommI2S.comm_pt1_corrupted_input(Top.Commitment.Some b)  (* If pt1 is corrupted, send its input to the simulator *)
          and transition WaitPt2Init(b, pt1, pt1_corrupted).        	(* Transition to waiting to learn whether Pt2 is corrupted *)
        }
        else {
          send CommI2S.comm_pt1_corrupted_input(Top.Commitment.None)  (* If pt2 is not corrupted, send None to the simulator *)
	  and transition WaitPt2Init(b, pt1, pt1_corrupted).          (* Transition to waiting to learn whether Pt2 is corrupted *)
        }
      }
    | *                => { fail. }
    end
  }

  state WaitPt2Init(b : bool, pt1 : port, pt1_corrupted : bool) {
    match message with
    (* Get init message from environment for pt2 *)
    | pt2@CommDir.Pt2.comm_party_init() => {
        send CommI2S.comm_pt2_init(pt2)				      (* Send the committer (pt2)'s port address to the simulator *)
        and transition WaitPt2Corruption(b, pt1, pt2, pt1_corrupted). (* Transition to waiting for simulator's decision to corrupt pt2 *)
      }
    | *                => { fail. }
    end
  }

  state WaitPt2Corruption(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool) {
    match message with
    (* Simulator responds to ideal functionality saying whether pt2 is corrupted *)
    | CommI2S.comm_pt2_corrupted(pt2_corrupted) => {
        if (pt1_corrupted = true /\ pt2_corrupted = true) { fail. }  (* If both parties are corrupted, fail. *)
        else {
	  send CommI2S.setup_done						  (* Tell simulator that the static corruption setup is done *)
     	  and transition WaitCommitReq(b, pt1, pt2, pt1_corrupted, pt2_corrupted).(* Transition to waiting for the 1st commit message *)
        }
      }
    | *                => { fail. }
    end
  }
  
  (* *)
  (* States pertaining to commitment protocol *)
  (* *)
  state WaitCommitReq(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool) {
    match message with
    (* Pt1 attempts to send a commitment of u to pt2. Message is adversarially delayed, i.e. forwarded to Sim, who oks delivery. *)
    | pt1'@CommDir.Pt1.comm_commit_req(pt2', u) => { (* Megan: Check that u = b? I'm unsure how the information flow changes given that IF has already forwarded b to Simulator. *)
        if (pt1' = pt1 /\ pt2' = pt2) {
        (*if (envport pt2) {*)
          send CommI2S.comm_sim_commit_req(pt1, pt2)  (* Ask simulator whether to deliver pt1's commit message to pt2 *)
	  and transition WaitCommitSim(b, pt1, pt2, pt1_corrupted, pt2_corrupted, u).  (* Transition to waiting for simulator's response *)
        }
        else { fail. }
      }
    | *                => { fail. }
    end
  }

  state WaitCommitSim(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool, u : bool) {
    match message with
    (* Simulator oks delivery of pt1's commitment message to pt2. *)
    | CommI2S.comm_sim_commit_rsp => {
        send CommDir.Pt2.comm_commit_rsp(pt1)@pt2  (* Deliver pt1's commitment message to pt2, which excludes u *)
	and transition WaitOpenReq(b, pt1, pt2, pt1_corrupted, pt2_corrupted, u).   (* Transition to waiting for pt1's open message *)
      }
    | *                => { fail. }
    end
  }

  state WaitOpenReq(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool, u : bool) {
    match message with
    (* Pt1 attempts to send an open message to pt2. Message is adversarially delayed, i.e. forwarded to Sim, who oks delivery. *)
    | pt1'@CommDir.Pt1.comm_open_req => {
        if (pt1' = pt1) {
          send CommI2S.comm_sim_open_req(u)        (* Ask simulator whether to deliver pt1's open message to pt2 *)
     	  and transition WaitOpenSim(b, pt1, pt2, pt1_corrupted, pt2_corrupted, u). (* Transition to waiting for simulator's response *)
        }
        else {
          fail.
        }
      }
    | *                => { fail. }
    end
  }

  state WaitOpenSim(b : bool, pt1 : port, pt2 : port, pt1_corrupted : bool, pt2_corrupted : bool, u : bool) {
    match message with
    (* Simulator oks delivery of pt1's open message, which includes u, to pt2. *)
    | CommI2S.comm_sim_open_rsp => {
        send CommDir.Pt2.comm_open_rsp(pt1, u)@pt2 (* Deliver pt1's open message to pt2, which includes u *)
	and transition Final.                      (* Transition to final state *)
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
