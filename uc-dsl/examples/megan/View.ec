(* View.ec *)

(* EasyCrypt definitions for tracking parties' view during a protocol *)
require import AllCore Distr UCBasicTypes.
require import Pke Cfptp.

(* Committer's view *)

type committer_elem = [
  C_c_env_port of port    (* Committer's client port in the environment *)
  | C_v_env_port of port  (* Verifier's client port in the environment *)
  | C_env_b of bool       (* Bit received from the environment *)
  | C_corrupted of bool   (* Whether the committer is corrupted *)
  | C_crs_fk of Cfptp.fkey (* forward key, received from CRS *)
  | C_crs_pk of Pke.pkey  (* public key, received from CRS *)
  | C_cmsg_x of Cfptp.D	(* Commit msg - random plaintext *)
  | C_cmsg_r of Pke.rand (* Commit msg - encryption randomness r *)
  | C_cmsg_rsample of Pke.rand (* Commit msg - randomness for oblivious encryption *)
  | C_cmsg_y of Cfptp.D (* Commit msg - result of sending x forward through CFPTP *)
  | C_cmsg_cb of Pke.ciphertext (* Commit msg - ciphertext c_b *)
  | C_cmsg_cnb of Pke.ciphertext (* Commit msg - ciphertext c_nb *)
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
  | V_crs_fk of Cfptp.fkey (* CRS *)
  | V_crs_pk of Pke.pkey (* CRS *)
].

type verifier = verifier_elem list.
