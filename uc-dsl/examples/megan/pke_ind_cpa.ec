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

(* Encryption scheme algorithms *)
op keygen : (pkey * skey) distr.
axiom keygen_ll: is_lossless keygen.
op enc(pk:pkey, m:plaintext, r:rand) : ciphertext.
op dec(sk:skey, c:ciphertext) : plaintext.

(* For checking correctness of encryption scheme *)
axiom correctness (pk: pkey, sk: skey, m: plaintext, r : rand):
  dec sk (enc pk m r) = m.

module type ADV_INDCPA = {
  (* choose a pair of plaintexts *)
  proc choose(): plaintext * plaintext 

  (* guess which plaintext was encrypted *)
  proc guess(c:ciphertext): bool
}.

(* IND-CPA Security Game, parametrized by an encryption scheme Enc and ind-cpa adversary *)
module INDCPA (Adv : ADV_INDCPA) = {
  proc main() : bool = {
    var b, b' : bool; 
    var x1, x2 : plaintext; 
    var c : ciphertext; 
    var r : rand; 
    var pk : pkey; var sk : skey;

    (pk, sk) <$ keygen;        (* generate keys for PKE *)
    r <$ drand;                (* select randomness used in PKE *)
    (x1, x2) <@ Adv.choose();  (* A chooses plaintexts x1/x2 *)
    b <$ {0,1};                (* choose boolean b *)
    c <@ enc pk (b ? x1 : x2) r; (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ Adv.guess(c);        (* give ciphertext to A, which returns guess *)
    return b = b';             (* see if A guessed correctly, winning game *)
  }
}.
