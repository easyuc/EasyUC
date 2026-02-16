(* CommitmentTypes.ec *)

(* This file contains useful types for the description of the commitment protocol in Commitment.uc. *)

(* Author: Megan Chen *)

(* Import required easycrypt files. *)
require import Cfptp Pke UCBasicTypes.

(* CRS *)
type crs = Cfptp.fkey * Pke.pkey. (* CRS in the real protocol *)
type sim_crs = Cfptp.fkey * Cfptp.bkey * Pke.pkey * Pke.skey. (* The simulated's CRS, plus Cfptp.bkey and Pke.skey *)

(* Commit Msg - y, c0, c1 *)
type commit_vals = Cfptp.D * Pke.ciphertext * Pke.ciphertext.

(* Open - b, x, rb, rnb *)
type open_vals = Cfptp.D * Pke.rand.
type open_vals_sim = Cfptp.D * Cfptp.D * Pke.rand * Pke.rand.
type open_rfake = Pke.rand.
