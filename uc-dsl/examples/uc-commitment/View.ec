(* View.ec *)

(* EasyCrypt definitions for tracking parties' view during a protocol *)
require import AllCore Distr UCBasicTypes.
require import Pke Cfptp Types.

(* Committer's view *)

type committer_elem = [
  | C_c_env_port of port    (* Committer's client port in the environment *)
  | C_v_env_port of port  (* Verifier's client port in the environment *)
  | C_env_b of bool       (* Bit received from the environment *)
  | C_corrupted of bool   (* Whether the committer is corrupted *)
  | C_crs of Types.crs (* CRS: Cfptp.fkey * Pke.pkey *)
  | C_cmsg of Types.commit_vals (* Cfptp.D * Pke.ciphertext * Pke.ciphertext *)
  | C_omsg of Types.open_vals	(* Open msg: Cfptp.D * Pke.rand *)
  | C_omsg_rfake of Types.open_rfake	(* Open msg - fake randomness *)
  | C_open_c_env_port of port (* Client port in environment requesting an open message *)
].

type committer = committer_elem list.

(* Verifier's view *)

type verifier_elem = [
  | V_c_env_port of port    (* Committer's client port in the environment *)
  | V_v_env_port of port  (* Verifier's client port in the environment *)
  | V_cmsg of Types.commit_vals (* Commit msg: Cfptp.D * Pke.ciphertext * Pke.ciphertext *)
  | V_corrupted of bool (* Whether the verifier is corrupted *)
  | V_omsg_b of bool (* Open msg - bit b *)
  | V_omsg of Types.open_vals (* Open msg: Cfptp.D * Pke.rand *)
  | V_omsg_rfake of Types.open_rfake (* Open msg - fake randomness *)
  | V_crs of Types.crs (* CRS: Cfptp.fkey * Pke.pkey *)
].

type verifier = verifier_elem list.
