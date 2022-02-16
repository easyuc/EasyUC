(* CommitmentTypes.ec *)

(* This file contains useful types for the description of the commitment protocol in Commitment.uc. *)

(* Author: Megan Chen *)

(* Import required easycrypt files. *)
require import Cfptp Pke UCBasicTypes.

(* CRS *)
type crs = Cfptp.fkey * Pke.pkey.
