(* Pke.ec *)

(* This describes a public key encryption scheme, capturing notion of IND-CPA security. *)

(* Author: Megan Chen *)

require import AllCore Distr DBool.

type pkey.
type skey.
type plaintext.
type ciphertext.

(* sample a random plaintext *)
op dplaintext : plaintext distr.
op zero : plaintext.

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
op oblivenc(pk:pkey, r:rand) : ciphertext.
op oblivenc_inv(pk:pkey, c: ciphertext) : rand. (* Can also include sk : skey, depending on scheme *)
op dec(sk:skey, c:ciphertext) : plaintext.

(* For checking correctness of encryption scheme *)
axiom correctness (pk: pkey, sk: skey, m: plaintext, r : rand):
  valid_keys (pk, sk) =>
  dec sk (enc pk m r) = m.

(* Oblivenc is a bijection *)
axiom oblivenc_bij (pk : pkey, r : rand):
  oblivenc_inv pk (oblivenc pk r) = r.

axiom oblivenc_inv_bij (pk : pkey, c : ciphertext):
  oblivenc pk (oblivenc_inv pk c) = c.

(* TODO: update indcpa to use oblivenc *)
module type ADV_INDCPA = {
  proc choose(pk : pkey) : plaintext
  proc main(pk : pkey, c : ciphertext) : bool
}.

module INDCPA_0(Adv : ADV_INDCPA) = { (* Always encrypts x0 *)
  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var r : rand;
    var x : plaintext;
    var b : bool;
    var c : ciphertext;
    (pk, sk) <$ dkeygen;         (* Generate keys for PKE *)
    r <$ drand;                  (* Select randomness used in PKE *)
    x <@ Adv.choose(pk);  	 (* Adv chooses a plaintext x *)
    c <- enc pk x r;             (* Always output an encryption of x *)
    b <@ Adv.main(pk, c);        (* Adv guesses which ciphertext was encrypted *)
    return b;
  }
}.

module INDCPA_1(Adv : ADV_INDCPA) = { (* Always encrypts x1*)
  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var r : rand;
    var x : plaintext;
    var b : bool;
    var c : ciphertext;
    (pk, sk) <$ dkeygen;         (* Generate keys for PKE *)
    r <$ drand;                  (* Select randomness used in PKE *)
    x <@ Adv.choose(pk);  	 (* Adv chooses plaintexts x *)
    c <- oblivenc pk r;          (* Always obliviously sample c *)
    b <@ Adv.main(pk, c);        (* Adv guesses which ciphertext was encrypted *)
    return b;
  }
}.

(* The *advantage* of an IND-CPA adversary Adv is

   `|Pr[INDCPA_0(Adv).main() @ &m : res] - Pr[INDCPA_1(Adv).main() @ &m : res]|

*)
