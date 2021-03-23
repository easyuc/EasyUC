(* Commitment.uc *)

(* This contains a two party UC F_com ideal functionality, as described in Figure 2 of Canetti Fischlin 01 (https://eprint.iacr.org/2001/055.pdf). This is a unit only containing one ideal functionality, no real functionalities (i.e. real protocol descriptions) and no simulators, and no extraneous interfaces *)

(* Direct interfaces, which are between ideal functionality and environment *)
direct CommDirPt1 {  (* Party 1, i.e. the Committer *)
  in  pt1@comm_commit_req(pt2 : port, u : bool)  (* request from pt1, asking to send the initial commitment to pt2 *)

  in pt1@comm_open_req()  (* message to pt2, asking to send the opening of the commitment to pt2 *)
}

direct CommDirPt2 {  (* Party 2, i.e. the Receiver *)
  out comm_commit_rsp(pt1 : port)@pt2  (* message to pt2, saying that pt1 has committed a message u *)

  out comm_open_rsp(pt1 : port, u : bool)@pt2  (* message to pt2, saying that pt1
    sent u to it *)
}

direct CommDir {
  Pt1 : CommDirPt1  (* Party 1 *)
  Pt2 : CommDirPt2  (* Party 2 *)
}

(* adversarial interface between ideal functionality and
   simulator, view from ideal functionality *)
adversarial CommI2S {
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
functionality CommIdeal implements CommDir CommI2S{
  initial state WaitCommitReq {
    match message with
    | pt1@CommDir.Pt1.comm_commit_req(pt2, u) => {
        if (envport pt2) {
          send CommI2S.comm_sim_commit_req(pt1, pt2)
	  and transition WaitCommitSim(pt1, pt2, u).
        }
        else { fail. }
      }
    | *                => { fail. }
    end
  }

  state WaitCommitSim(pt1 : port, pt2 : port, u : bool) {
    match message with
    | CommI2S.comm_sim_commit_rsp => {
        send CommDir.Pt2.comm_commit_rsp(pt1)@pt2
	and transition WaitOpenReq(pt1, pt2, u).
      }
    | *                => { fail. }
    end
  }

  state WaitOpenReq(pt1 : port, pt2 : port, u: bool) {
    match message with
    | pt1'@CommDir.Pt1.comm_open_req() => {
        if (pt1' = pt1) {
          send CommI2S.comm_sim_open_req(u)
     	  and transition WaitOpenSim(pt1, pt2, u).
        }
        else {
          fail.
        }
      }
    | *                => { fail. }
    end
  }

  state WaitOpenSim(pt1 : port, pt2 : port, u : bool) {
    match message with
    | CommI2S.comm_sim_open_rsp => {
        send CommDir.Pt2.comm_open_rsp(pt1, u)@pt2
	and transition Final.
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
