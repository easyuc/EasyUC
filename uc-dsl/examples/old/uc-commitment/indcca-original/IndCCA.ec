(* IndCCA.ec *)

(* This describes a public key encryption scheme, capturing notion of
   IND-CCA security. *)

require import AllCore Distr DBool FSet.

type pkey.        (* public key *)
type skey.        (* secret key *)
type plaintext.   (* plain text *)
type ciphertext.  (* cipher text *)
type rand.        (* randomness *)

(* uniform, full and lossless distribution on plain texts

   so plaintext is finite *)

op dplaintext : plaintext distr.

axiom dplaintext_uni : is_uniform dplaintext.
axiom dplaintext_fu  : is_full dplaintext.
axiom dplaintext_ll  : is_lossless dplaintext.

(* uniform, full and lossless distribution on randomness

   so rand is finite *)

op drand : rand distr.

axiom drand_uni : is_uniform drand.
axiom drand_fu  : is_full drand.
axiom drand_ll  : is_lossless drand.

(* lossless distribution on public/secret key pairs *)

op dkeygen : (pkey * skey) distr.

axiom keygen_ll : is_lossless dkeygen.

(* test if key pair is in support of dkeygen *)

op valid_keys (keys : pkey * skey) : bool = support dkeygen keys.

(* encrypt plaintext relative to randomness *)

op enc(pk : pkey, m : plaintext, r : rand) : ciphertext.

(* decrypt cipher text (not needed randomness) *)

op dec(sk : skey, c : ciphertext) : plaintext.

(* correctness of encryption scheme *)

axiom correctness (pk : pkey, sk : skey, m : plaintext, r : rand):
  valid_keys (pk, sk) => dec sk (enc pk m r) = m.

(* oblivious encryption of randomness, plus inverse *)

op obliv_enc(pk : pkey, r : rand) : ciphertext.
op obliv_enc_inv(pk : pkey, c : ciphertext) : rand.

(* obliv_enc pk is a bijection, and so rand and ciphertext have
   the same size *)

axiom obliv_enc_bij (pk : pkey, r : rand):
  obliv_enc_inv pk (obliv_enc pk r) = r.
axiom obliv_enc_inv_bij (pk : pkey, c : ciphertext):
  obliv_enc pk (obliv_enc_inv pk c) = c.

(* IND-CCA oracle *)

module type OR_INDCCA = {
  (* initialization, given key pair *)

  proc init(keys : pkey * skey) : unit

  (* encrypt a plaintext using stored public key and fresh randomness *)

  proc enc(m : plaintext) : ciphertext

  (* decrypt a cipher text, yielding optional plaintext that is
     None if c was previously produced by enc, and is Some of
     the decryption using stored secret key, otherwise *)

  proc dec(c : ciphertext) : plaintext option
}.

(* we have two oracle implementations *)

module OrIndCCA1 : OR_INDCCA = {
  var pk : pkey
  var sk : skey
  var cs : ciphertext fset

  proc init(keys : pkey * skey) : unit = {
    pk <- keys.`1; sk <- keys.`2; cs <- fset0;
  }

  proc enc(m : plaintext) : ciphertext = {
    var r : rand; var c : ciphertext;
    r <$ drand;
    c <- enc pk m r;  (* normal encryption *)
    cs <- cs `|` fset1 c;
    return c;
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- Some (dec sk c);  (* normal decryption *)
    }
    return x;
  }
}.

module OrIndCCA2 : OR_INDCCA = {
  var pk : pkey
  var sk : skey
  var cs : ciphertext fset

  proc init(pk_ : pkey, sk_ : skey) : unit = {
    pk <- pk_; sk <- sk_; cs <- fset0;
  }

  proc enc(m : plaintext) : ciphertext = {
    var r : rand; var c : ciphertext;
    r <$ drand;
    c <- obliv_enc pk r;  (* oblivious encryption *)
    cs <- cs `|` fset1 c;
    return c;
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- Some (dec sk c);  (* normal decryption *)
    }
    return x;
  }
}.

(* IND-CCA adversary, parameterized by IND-CCA oracle

   is given public key, and returns boolean judgment *)

module type ADV_INDCCA (Or : OR_INDCCA) = {
  proc main(pk : pkey) : bool {Or.enc, Or.dec}
}.

module IndCCA(Or : OR_INDCCA, Adv : ADV_INDCCA) = {
  module A = Adv(Or)  (* connect adversary and oracle *)

  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var b : bool;
    (pk, sk) <$ dkeygen;  (* generate keypair *)
    Or.init(pk, sk);      (* initialize oracle *)
    b <@ A.main(pk);      (* invoke adversary, which returns judgment *)
    return b;
  }
}.

(* apply IndCCA to the two INDCCA oracle implementations, yielding
   the two IND-CCA games: *)

module IndCCA1 = IndCCA(OrIndCCA1).
module IndCCA2 = IndCCA(OrIndCCA2).

(* The *advantage* of an IND-CCA adversary Adv is

   `|Pr[IndCCA1(Adv).main() @ &m : res] - Pr[IndCCA2(Adv).main() @ &m : res]|
*)
