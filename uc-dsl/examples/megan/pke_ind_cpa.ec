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
axiom drand_uni : is_uniform drand.
axiom drand_fu : is_full drand.
axiom drand_ll  : is_lossless drand.

(* Encryption scheme algorithms *)
op dkeygen : (pkey * skey) distr.
axiom keygen_ll: is_lossless dkeygen.
(* what other axioms on dkeygen? *)

pred valid_keys (keys: pkey * skey) = support dkeygen keys.

op enc(pk:pkey, m:plaintext, r:rand) : ciphertext.
op dec(sk:skey, c:ciphertext) : plaintext.

(* For checking correctness of encryption scheme *)
axiom correctness (pk: pkey, sk: skey, m: plaintext, r : rand):
  valid_keys (pk, sk) =>
  dec sk (enc pk m r) = m.

module type ADV_INDCPA = {
  (* choose a pair of plaintexts *)
  proc choose(pk : pkey): plaintext * plaintext

  (* guess which plaintext was encrypted *)
  proc guess(c : ciphertext): bool
}.

(* IND-CPA Security Game, parametrized by an encryption scheme Enc and ind-cpa adversary *)
module INDCPA (Adv : ADV_INDCPA) = {
  proc main() : bool = {
    var b, b' : bool;
    var x1, x2 : plaintext;
    var c : ciphertext;
    var r : rand;
    var pk : pkey; var sk : skey;

    (pk, sk) <$ dkeygen;         (* generate keys for PKE *)
    r <$ drand;                  (* select randomness used in PKE *)
    (x1, x2) <@ Adv.choose(pk);  (* A chooses plaintexts x1/x2 *)
    b <$ {0,1};                  (* choose boolean b *)
    c <- enc pk (b ? x1 : x2) r; (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ Adv.guess(c);          (* give ciphertext to A, which returns guess *)
    return b = b';               (* see if A guessed correctly, winning game *)
  }
}.
