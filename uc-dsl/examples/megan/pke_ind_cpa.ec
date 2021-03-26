(* pke_ind_cpa.ec *)

(* This captures in the IND-CPA security of a public key encryption scheme. *)

(* Author: Megan Chen *)

require import AllCore Distr DBool.

type pkey.
type skey.
type plaintext.
type ciphertext.

op ciph_def : ciphertext.  (* default ciphertext *)

(* Encryption oracle limit before game's encryption.
   This says limit_pre has type int and the axiom ge0_limit_pre says
   limit_pre is non-negative *)
op limit_pre : {int | 0 <= limit_pre} as ge0_limit_pre.

(* Encryption oracle limit after game's encryption. *)
op limit_post : {int | 0 <= limit_post} as ge0_limit_post.

module type ENC = {
  proc key_gen(): pkey * skey
  proc enc(k:pkey, p:plaintext): ciphertext
  proc dec(k:skey, c:ciphertext): plaintext
}.

(* For checking correctness of encryption scheme *)
module Correctness (Enc : ENC) = {
  proc main(x : plaintext) : bool = {
    var pk : pkey; var sk : skey; var c : ciphertext; var y : plaintext;
    (pk, sk) <@ Enc.key_gen();
    c <@ Enc.enc(pk, x);
    y <@ Enc.dec(sk, c);
    return x = y;
  }
}.

(* module type of encryption oracles *)
module type EO = {
  (* initialization *)
  proc * init() : unit

  (* encryption of text by adversary before game's encryption *)
  proc enc_pre(x : plaintext) : ciphertext

  (* one-time encryption of text by game *)
  proc genc(x : plaintext) : ciphertext

  (* encryption of text by adversary after game's encryption *)
  proc enc_post(x : plaintext) : ciphertext
}.

(* standard encryption oracle, constructed from an encryption
   scheme *)
module EncO (Enc : ENC) : EO = {
  var pk : pkey
  var sk : skey
  var ctr_pre : int
  var ctr_post : int

  proc init() : unit = {
    (pk, sk) <@ Enc.key_gen();
    ctr_pre <- 0; ctr_post <- 0;
  }

  proc enc_pre(x : plaintext) : ciphertext = {
    var c : ciphertext;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      c <@ Enc.enc(pk, x);
    }
    else {
      c <- ciph_def;  (* default result *)
    }  
    return c;
  }

  proc genc(x : plaintext) : ciphertext = {
    var c : ciphertext;
    c <@ Enc.enc(pk, x);
    return c;
  }

  proc enc_post(x : plaintext) : ciphertext = {
    var c : ciphertext;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      c <@ Enc.enc(pk, x);
    }
    else {
      c <- ciph_def;  (* default result *)
    }  
    return c;
  }
}.

module type ADV_INDCPA (EncO : EO) = {
  (* choose a pair of plaintexts *)
  proc choose(): plaintext * plaintext {EncO.enc_pre}

  (* guess which plaintext was encrypted *)
  proc guess(c:ciphertext): bool {EncO.enc_post}
}.

(* IND-CPA Security Game, parametrized by an encryption scheme Enc and ind-cpa adversary *)
module INDCPA (Enc : ENC, Adv : ADV_INDCPA) = {
  module EO = EncO(Enc)        (* make EO from Enc *)
  module A = Adv(EO)           (* connect Adv to EO *)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : plaintext; var c : ciphertext;
    EO.init();                 (* initialize EO *)
    (x1, x2) <@ A.choose();    (* let A choose plaintexts x1/x2 *)
    b <$ {0,1};                (* choose boolean b *)
    c <@ EO.genc(b ? x1 : x2); (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ A.guess(c);          (* give ciphertext to A, which returns guess *)
    return b = b';             (* see if A guessed correctly, winning game *)
  }
}.
