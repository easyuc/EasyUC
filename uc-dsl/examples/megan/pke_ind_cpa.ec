(* pke_ind_cpa.ec *)

(* This captures in the IND-CPA security of a public key encryption scheme. *)

(* Author: Megan Chen *)

require import AllCore Distr DBool.

type pkey.
type skey.
type plaintext.
type ciphertext.

(* randomness *)
type rand.
op drand : rand distr.
axiom dexp_uni : is_uniform drand.
axiom drand_ll  : is_lossless drand.

op ciph_def : ciphertext.  (* default ciphertext *)

module type ENC = {
  proc keygen() : pkey * skey
  proc enc(pk:pkey, m:plaintext, r:rand)  : ciphertext
  proc dec(sk:skey, c:ciphertext) : plaintext
}.

(* For checking correctness of encryption scheme *)
module Correctness (Enc : ENC) = {
  proc main(x : plaintext) : bool = {
    var pk : pkey; var sk : skey; var c : ciphertext; var y : plaintext; var r : rand;
    (pk, sk) <@ Enc.keygen();
    c <@ Enc.enc(pk, x, r);
    y <@ Enc.dec(sk, c);
    return x = y;
  }
}.

module type ADV_INDCPA = {
  (* choose a pair of plaintexts *)
  proc choose(): plaintext * plaintext 

  (* guess which plaintext was encrypted *)
  proc guess(c:ciphertext): bool
}.

(* IND-CPA Security Game, parametrized by an encryption scheme Enc and ind-cpa adversary *)
module INDCPA (Enc : ENC, Adv : ADV_INDCPA) = {
  proc main() : bool = {
    var b, b' : bool; 
    var x1, x2 : plaintext; 
    var c : ciphertext; 
    var r : rand; 
    var pk : pkey;
    var sk : skey;

    (pk, sk) <@ Enc.keygen();  (* generate keys for PKE *)
    r <$ drand;                (* select randomness used in PKE *)
    (x1, x2) <@ Adv.choose();  (* A chooses plaintexts x1/x2 *)
    b <$ {0,1};                (* choose boolean b *)
    c <@ Enc.enc(pk, b ? x1 : x2, r); (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ Adv.guess(c);        (* give ciphertext to A, which returns guess *)
    return b = b';             (* see if A guessed correctly, winning game *)
  }
}.
