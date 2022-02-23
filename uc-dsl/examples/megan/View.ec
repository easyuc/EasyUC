(* View.ec *)

(* EasyCrypt definitions for tracking parties' view during a protocol *)
require import AllCore Distr UCBasicTypes.
require import Pke Cfptp Types.

(* Committer's view *)

type committer_elem = [
  C_c_env_port of port    (* Committer's client port in the environment *)
  | C_v_env_port of port  (* Verifier's client port in the environment *)
  | C_env_b of bool       (* Bit received from the environment *)
  | C_corrupted of bool   (* Whether the committer is corrupted *)
  | C_crs of Types.crs (* CRS: Cfptp.fkey * Pke.pkey *)
  | C_omsg_x of Cfptp.D	(* Open msg - random plaintext *)
  | C_omsg_r of Pke.rand (* Open msg - encryption randomness r *)
  | C_omsg_rsample of Pke.rand (* Open msg - randomness for oblivious encryption *)
  | C_cmsg of Types.commit_vals (* Cfptp.D * Pke.ciphertext * Pke.ciphertext *)
  | C_open_c_env_port of port (* Client port in environment requesting an open message *)
].

type committer = committer_elem list.

(* Verifier's view *)

type verifier_elem = [
  V_c_env_port of port    (* Committer's client port in the environment *)
  | V_v_env_port of port  (* Verifier's client port in the environment *)
  | V_cmsg_y of Cfptp.D (* Commit msg - value in permutation domain *)
  | V_cmsg_cfalse of Pke.ciphertext (* Commit msg - ciphertext c_false *)
  | V_cmsg_ctrue of Pke.ciphertext (* Commit msg - ciphertext c_true *)
  | V_corrupted of bool (* Whether the verifier is corrupted *)
  | V_omsg_b of bool (* Open msg - bit b *)
  | V_omsg_x of Cfptp.D (* Open msg - value in permutation domain *)
  | V_omsg_rb of Pke.rand (* Open msg - encryption randomness *)
  | V_omsg_rnb of Pke.rand (* Open msg - (unused) encryption randomness *)
  | V_crs of Types.crs (* CRS: Cfptp.fkey * Pke.pkey *)
].

type verifier = verifier_elem list.
