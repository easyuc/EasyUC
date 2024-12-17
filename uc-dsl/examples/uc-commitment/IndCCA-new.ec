(* IndCCA.ec *)

(* this theory describes a public key encryption scheme capturing
   the notion of multiple run IND-CCA security

   it also defines a "pre-image game" along with a reduction of its
   security to IND-CCA security *)

prover quorum=2 ["Z3" "Alt-Ergo"].

require import AllCore Distr List FSet FMap FelTactic.
require import StdOrder. import RealOrder.
require import StdBigop. import Bigreal BRA.
require import StdRing. import RField.

(* BEGINNING OF THEORY PARAMETERS (plus associated lemmas) *)

(* the type of plain texts has pt_siz elements *)

type plaintext.

op pt_elems : plaintext fset.  (* finite set *)

(* so by this axiom, pt_elems is exactly the elements of plaintext: *)

axiom pt_elems (pt : plaintext) : pt \in pt_elems.

op pt_siz : int = card pt_elems.

op pt_def : plaintext.  (* default plain text *)

lemma gt0_pt_siz : 0 < pt_siz.
proof.
rewrite /pt_siz ltzE /=.
have -> : 1 = card (fset1 pt_def) by rewrite fcard1.
rewrite subset_leq_fcard => x.
rewrite in_fset1 => ->.
rewrite pt_elems.
qed.

(* the type of random values has rd_siz elements *)

type rand.

op rd_elems : rand fset.

(* so by this axiom, rd_elems is exactly the elements of rand: *)

axiom rd_elems (r : rand) : r \in rd_elems.

op rd_siz : int = card rd_elems.

op rd_def : rand.  (* default randomness *)

lemma gt0_rd_siz : 0 < rd_siz.
proof.
rewrite /rd_siz ltzE /=.
have -> : 1 = card (fset1 rd_def) by rewrite fcard1.
rewrite subset_leq_fcard => x.
rewrite in_fset1 => ->.
rewrite rd_elems.
qed.

(* create a full, uniform and lossless distribution on rand *)

op drand : rand distr = duniform (elems rd_elems).

lemma drand1E (x : rand) :
  mu1 drand x = 1%r / rd_siz%r.
proof.
rewrite duniform1E_uniq 1:uniq_elems.
by rewrite -memE rd_elems /= -cardE.
qed.

lemma drand_fu : is_full drand.
proof.
rewrite duniform_fu => x.
rewrite -memE rd_elems.
qed.

lemma drand_ll : is_lossless drand.
proof.
rewrite duniform_ll.
case (elems rd_elems = []) => [/elems_eq_fset0 rd_elems_eq_fset0 | //].
have : rd_def \in fset0 by rewrite -rd_elems_eq_fset0 rd_elems.
by rewrite in_fset0.
qed.

(* the type of cipher texts *)

type ciphertext.

op ct_def : ciphertext.  (* default cipher text *)

(* public/secret key pairs *)

type pkey.  (* public key *)
type skey.  (* secret key *)

(* lossless distribution on key pairs

   so choosing a keypair will always succeed, but we don't
   axiomatize anything else about the distribution *)

op dkeygen : (pkey * skey) distr.

axiom dkeygen_ll : is_lossless dkeygen.

(* test if key pair is in support of dkeygen (which should
   be true iff the key pair is valid according to the
   encrytion scheme) *)

op valid_keys (keys : pkey * skey) : bool = support dkeygen keys.

op valid_pkey (pk : pkey) : bool =
  exists (sk : skey), valid_keys (pk, sk).

op valid_skey (sk : skey) : bool =
  exists (pk : pkey), valid_keys (pk, sk).

(* encrypt plain text relative to randomness *)

op enc (pk : pkey, m : plaintext, r : rand) : ciphertext.

(* decrypt cipher text (randomness not needed); returns None
   when decryption fails, i.e., cipher text is invalid *)

op dec (sk : skey, c : ciphertext) : plaintext option.

(* correctness of encryption scheme *)

axiom correctness (pk : pkey, sk : skey, m : plaintext, r : rand) :
  valid_keys (pk, sk) => dec sk (enc pk m r) = Some m.

(* oblivious encryption from randomness *)

op obliv_enc (pk : pkey, r : rand) : ciphertext.

(* probabilistic inverse to oblivious encryption *)

op obliv_enc_inv (pk : pkey, c : ciphertext) : rand distr.

(* for any valid pk, ciphertext c and randomness r, we want that r is
   in the support of obliv_enc_inv pk c exactly when obliv_enc pk r =
   c *)

axiom obliv_enc_inv_support (pk : pkey, c : ciphertext, r : rand) :
  support (obliv_enc_inv pk c) r <=> obliv_enc pk r = c.

(* consequently, we have: *)

lemma obliv_enc_inv_support_obliv_enc (pk : pkey, r : rand) :
  valid_pkey pk => support (obliv_enc_inv pk (obliv_enc pk r)) r.
proof.
move => vpk_pk.
by rewrite obliv_enc_inv_support.
qed.

(* for any valid pk and ciphertext c, we want that the distribution
   obliv_enc_inv pk c is lossless (so it is safe for a procedure to
   sample from it) and uniform (but not full) *)

axiom obliv_enc_inv_ll (pk : pkey, c : ciphertext) :
  is_lossless (obliv_enc_inv pk c).

axiom obliv_enc_uni (pk : pkey, c : ciphertext) :
  is_full (obliv_enc_inv pk c).

lemma mu_cancel_obliv_enc_inv_obliv_enc_eq1 (pk : pkey, c : ciphertext) :
  valid_pkey pk =>
  mu (obliv_enc_inv pk c) (fun r => obliv_enc pk r = c) = 1%r.
proof.
move => vpk_pk.
rewrite eq1_mu // 1:obliv_enc_inv_ll => r support_obliv_enc_inv_pk_c_r /=.
by rewrite -obliv_enc_inv_support.
qed.

(* for use in the security bound of the preimage game *)

op mu_obliv_enc_dec_exact (pk : pkey, sk : skey, m : plaintext) =
  mu drand (fun r => dec sk (obliv_enc pk r) = Some m).

(* ***TODO***: define this in terms of pt_siz for some IND-CCA
   scheme or schemes *)

op mu_obliv_enc_dec_exact_ub : real.

axiom mu_obliv_enc_dec_exact_ub (pk : pkey, sk : skey) :
  valid_keys (pk, sk) =>
  mu_obliv_enc_dec_exact pk sk pt_def <= mu_obliv_enc_dec_exact_ub.

(* number of allowed runs of the encryption procedure of the IND-CCA
   oracle (or the obliv procedure in the preimage oracle) before a
   default cipher text is returned *)

op runs : int.

axiom ge0_runs : 0 <= runs.

(* END OF THEORY PARAMETERS (and asociated lemmas) *)

(* IND-CCA oracle *)

module type OR_INDCCA = {
  (* initialization, given key pair *)

  proc init(keys : pkey * skey) : unit

  (* encrypt a plaintext using stored public key and fresh randomness
     r, returning the ciphertext c along with randomness r' in the
     support of obliv_enc_inv pk c (see OrIndCCA1 and OrIndCCA2 for
     how this r' is chosen); returns (ct_def, rd_def) if runs of enc
     have been exhausted *)

  proc enc(m : plaintext) : ciphertext * rand

  (* decrypt a cipher text, yielding optional plaintext that is
     None if c was previously produced by enc, and is
     the decryption using stored secret key, otherwise *)

  proc dec(c : ciphertext) : plaintext option
}.

(* we have two oracle implementations *)

module OrIndCCA1 : OR_INDCCA = {
  var pk  : pkey
  var sk  : skey
  var cs  : ciphertext fset  (* results of encryption oracle *)
  var ctr : int              (* runs so far *)

  proc init(pk_ : pkey, sk_ : skey) : unit = {
    pk <- pk_; sk <- sk_; cs <- fset0; ctr <- 0;
  }

  proc enc(m : plaintext) : ciphertext * rand = {
    var r, r' : rand; var c : ciphertext;
    if (ctr < runs) {  (* another run possible? *)
      r <$ drand;
      c <- enc pk m r;  (* normal encryption *)
      cs <- cs `|` fset1 c;
      r' <$ obliv_enc_inv pk c;  (* sample from obliv_enc_inv pk c *)
      ctr <- ctr + 1;
    }
    else {
      c <- ct_def; r' <- rd_def;
    }
    return (c, r');
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- dec sk c;  (* normal decryption, could be None *)
    }
    return x;
  }
}.

module OrIndCCA2 : OR_INDCCA = {
  var pk  : pkey
  var sk  : skey
  var cs  : ciphertext fset
  var ctr : int

  proc init(pk_ : pkey, sk_ : skey) : unit = {
    pk <- pk_; sk <- sk_; cs <- fset0; ctr <- 0;
  }

  proc enc(m : plaintext) : ciphertext * rand = {
    var r, r' : rand; var c : ciphertext;
    if (ctr < runs) {
      r <$ drand;
      c <- obliv_enc pk r;  (* oblivious encryption *)
      cs <- cs `|` fset1 c;
      r' <- r;  (* use actual randomness *)
      ctr <- ctr + 1;
    }
    else {
      c <- ct_def; r' <- rd_def;
    }
    return (c, r');
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- dec sk c;  (* normal decryption *)
    }
    return x;
  }
}.

(* IND-CCA adversary, parameterized by IND-CCA oracle

   is given public key, and returns boolean judgment;
   it may not reinitialize oracle *)

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

   `|Pr[IndCCA1(Adv).main() @ &m : res] -
     Pr[IndCCA2(Adv).main() @ &m : res]|
*)

(* pre-image security *)

module type OR_PI = {
  (* initialization, given key pair *)

  proc init(keys : pkey * skey) : unit

  (* obliviously generate a cipher text using stored public key
     and fresh randomness; returns ct_def if runs have been
     exhausted *)

  proc obliv() : ciphertext

  (* decrypt a cipher text, yielding optional plaintext that is None
     if c was previously produced by obliv, and is the decryption
     using stored secret key, otherwise *)

  proc dec(c : ciphertext) : plaintext option

  (* test whether enc of stored public key, x and r yields
     one of the ciphertexts previously produced by obliv *)

  proc check_preimage(x : plaintext, r : rand) : bool
}.

module OrPI : OR_PI = {
  var pk  : pkey
  var sk  : skey
  var cs  : ciphertext fset
  var ctr : int

  proc init(pk_ : pkey, sk_ : skey) : unit = {
    pk <- pk_; sk <- sk_; cs <- fset0; ctr <- 0;
  }

  proc obliv() : ciphertext = {
    var r : rand; var c : ciphertext;
    if (ctr < runs) {
      r <$ drand;
      c <- obliv_enc pk r;
      cs <- cs `|` fset1 c;
      ctr <- ctr + 1;
    }
    else {
      c <- ct_def;
    }
    return c;
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- dec sk c;
    }
    return x;
  }

  proc check_preimage(x : plaintext, r : rand) : bool = {
    return enc pk x r \in cs;
  }
}.

module type ADV_PI (Or : OR_PI) = {
  proc main(pk : pkey) : plaintext * rand {Or.obliv, Or.dec}
}.

module PreImage(Adv : ADV_PI) = {
  module A = Adv(OrPI)  (* connect adversary and oracle *)

  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var x : plaintext; var r : rand;
    var b : bool;
    (pk, sk) <$ dkeygen;             (* generate keypair *)
    OrPI.init(pk, sk);               (* initialize oracle *)
    (x, r) <@ A.main(pk);            (* invoke adversary *)
    b <@ OrPI.check_preimage(x, r);  (* see if adversary won *)
    return b;
  }
}.

(* construct an IND-CCA adversary from a preimage adversary;
   for use in security upper bound *)

module AdvPI2IndCCAAdv(AdvPI : ADV_PI, IndCCAOr : OR_INDCCA) = {
  module OrPI : OR_PI = {
    var pk  : pkey
    var cs  : ciphertext fset
    var ctr : int

    (* sk_ won't be real, so ignore it: *)

    proc init(pk_ : pkey, sk_ : skey) : unit = {
      pk <- pk_; cs <- fset0; ctr <- 0;
    }

    proc obliv() : ciphertext = {
      var r : rand; var c : ciphertext;
      if (ctr < runs) {
        (* use IndCCAOr.enc; ignore r *)
        (c, r) <@ IndCCAOr.enc(pt_def);
        cs <- cs `|` fset1 c;
        ctr <- ctr + 1;
      }
      else {
        c <- ct_def;
      }
      return c;
    }

    proc dec(c : ciphertext) : plaintext option = {
      var x : plaintext option;
      x <@ IndCCAOr.dec(c);  (* use IndCCAOr.dec *)
      return x;
    }

    proc check_preimage(x : plaintext, r : rand) : bool = {
      return enc pk x r \in cs;
    }
  }

  module A = AdvPI(OrPI)

  proc main(pk : pkey) : bool = {
    var b : bool; var x : plaintext; var r : rand;
    OrPI.init(pk, witness);
    (x, r) <@ A.main(pk);
    b <@ OrPI.check_preimage(x, r);
    return b /\ x <> pt_def;  (* not second conjunct *)
  }
}.

(* start security proof *)

section.

declare module
  AdvPI <: ADV_PI{-OrPI, -OrIndCCA1, -OrIndCCA2, -AdvPI2IndCCAAdv}.

(* in our first step, we use up-to bad reasoning; this game
   is like PreImage except it detects the bad event *)

local module OrPI_bad1 : OR_PI = {
  var pk  : pkey
  var sk  : skey
  var cs  : ciphertext fset
  var ctr : int
  var bad : bool

  proc init(pk_ : pkey, sk_ : skey) : unit = {
    pk <- pk_; sk <- sk_; cs <- fset0; ctr <- 0; bad <- false;
  }

  proc obliv() : ciphertext = {
    var r : rand; var c : ciphertext;
    if (ctr < runs) {
      r <$ drand;
      c <- obliv_enc pk r;
      cs <- cs `|` fset1 c;
      ctr <- ctr + 1;
    }
    else {
      c <- ct_def;
    }
    return c;
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- dec sk c;
    }
    return x;
  }

  proc check_preimage(x : plaintext, r : rand) : bool = {
    var b : bool;
    if (enc pk x r \in cs) {
      b <- true;
      if (x = pt_def) {  (* bad event occurs *)
        bad <- true;
      }
    }
    else {
      b <- false;
    }
    return b;
  }
}.

local module PI_bad1 = {
  module A = AdvPI(OrPI_bad1)

  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var x : plaintext; var r : rand;
    var b : bool;
    (pk, sk) <$ dkeygen;
    OrPI_bad1.init(pk, sk);
    (x, r) <@ A.main(pk);
    b <@ OrPI_bad1.check_preimage(x, r);
    return b;
  }
}.

local lemma PreImage_AdvPI_PI_bad1 &m :
  Pr[PreImage(AdvPI).main() @ &m : res] = Pr[PI_bad1.main() @ &m : res].
proof.
byequiv => //; proc.
call (_ : ={pk, sk, cs, ctr}(OrPI, OrPI_bad1)); first auto.
call (_ : ={pk, sk, cs, ctr}(OrPI, OrPI_bad1)); first 2 sim.
call (_ : ={pk_, sk_} ==> ={pk, sk, cs, ctr}(OrPI, OrPI_bad1)); first sim.
auto.
qed.

(* this game changes the result when the bad event occurs *)

local module OrPI_bad2 : OR_PI = {
  var pk  : pkey
  var sk  : skey
  var cs  : ciphertext fset
  var ctr : int
  var bad : bool

  proc init(pk_ : pkey, sk_ : skey) : unit = {
    pk <- pk_; sk <- sk_; cs <- fset0; ctr <- 0; bad <- false;
  }

  proc obliv() : ciphertext = {
    var r : rand; var c : ciphertext;
    if (ctr < runs) {
      r <$ drand;
      c <- obliv_enc pk r;
      cs <- cs `|` fset1 c;
      ctr <- ctr + 1;
    }
    else {
      c <- ct_def;
    }
    return c;
  }

  proc dec(c : ciphertext) : plaintext option = {
    var x : plaintext option;
    if (mem cs c) {
      x <- None;
    }
    else {
      x <- dec sk c;
    }
    return x;
  }

  proc check_preimage(x : plaintext, r : rand) : bool = {
    var b : bool;
    if (enc pk x r \in cs) {
      if (x = pt_def) {
        b <- false;   (* we return false when normally true *)
        bad <- true;  (* would be returned *)
      }
      else {
        b <- true;
      }
    }
    else {
      b <- false;
    }
    return b;
  }
}.

local module PI_bad2 = {
  module A = AdvPI(OrPI_bad2)

  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var x : plaintext; var r : rand;
    var b : bool;
    (pk, sk) <$ dkeygen;
    OrPI_bad2.init(pk, sk);
    (x, r) <@ A.main(pk);
    b <@ OrPI_bad2.check_preimage(x, r);
    return b;
  }
}.

local lemma PI_bad1_2 &m :
  `|Pr[PI_bad1.main() @ &m : res] - Pr[PI_bad2.main() @ &m : res]| <=
  Pr[PI_bad2.main() @ &m : OrPI_bad2.bad].
proof.
byequiv  (* up-to bad form of byequiv *)
  (_ :
   ={glob AdvPI} ==>
   ={bad}(OrPI_bad1, OrPI_bad2) /\ (! OrPI_bad2.bad{2} => ={res})) :
  OrPI_bad1.bad => //.
proc.
seq 3 3 : (={x, r} /\ ={pk, sk, cs, ctr, bad}(OrPI_bad1, OrPI_bad2)).
call (_ : ={pk, sk, cs, ctr, bad}(OrPI_bad1, OrPI_bad2)); first 2 sim.
call
  (_ :
   ={pk_, sk_} ==>
   ={pk, sk, cs, ctr, bad}(OrPI_bad1, OrPI_bad2)); first sim.
auto.
inline*; auto.
smt().
qed.

local lemma PreImage_AdvPI_PI_bad2 &m :
  `|Pr[PreImage(AdvPI).main() @ &m : res] -
    Pr[PI_bad2.main() @ &m : res]| <=
  Pr[PI_bad2.main() @ &m : OrPI_bad2.bad].
proof.
rewrite (PreImage_AdvPI_PI_bad1 &m) (PI_bad1_2 &m).
qed.

(* for upper-bounding the probability of that bad event happening *)

local module PI_bad_ub = {
  module Or : OR_PI  = {
    var pk  : pkey
    var sk  : skey
    var cs  : ciphertext fset
    var ctr : int
    var bad : bool

    proc init(pk_ : pkey, sk_ : skey) : unit = {
      pk <- pk_; sk <- sk_; cs <- fset0; ctr <- 0; bad <- false;
    }

    proc obliv() : ciphertext = {
      var r : rand; var c : ciphertext;
      if (ctr < runs) {
        r <$ drand;
        c <- obliv_enc pk r;
        if (dec sk c = Some pt_def) {  (* now we set the bad event here,*)
          bad <- true;                 (* earlier and potentially more *)
        }                              (* often *)
        cs <- cs `|` fset1 c;
        ctr <- ctr + 1;
      }
      else {
        c <- ct_def;
      }
      return c;
    }

    proc dec(c : ciphertext) : plaintext option = {
      var x : plaintext option;
      if (mem cs c) {
        x <- None;
      }
      else {
        x <- dec sk c;
      }
      return x;
    }

    (* no longer used: *)

    proc check_preimage(x : plaintext, r : rand) : bool = {
      return true;
    }
  }

  module A = AdvPI(Or)

  proc main() : bool = {
    var pk : pkey; var sk : skey;
    var x : plaintext; var r : rand;
    var b : bool;
    (pk, sk) <$ dkeygen;
    Or.init(pk, sk);
    (x, r) <@ A.main(pk);
    return Or.bad;
  }
}.

local lemma PI_bad2_ub &m :
  Pr[PI_bad2.main() @ &m : OrPI_bad2.bad] <=
  Pr[PI_bad_ub.main() @ &m : PI_bad_ub.Or.bad].
proof.
byequiv => //.
proc.
seq 2 2 : 
  (={pk, sk, glob AdvPI} /\
   ={pk, sk, cs, ctr, bad}(OrPI_bad2, PI_bad_ub.Or) /\
   pk{1} = OrPI_bad2.pk{1} /\ sk{1} = OrPI_bad2.sk{1} /\
   OrPI_bad2.cs{1} = fset0 /\ valid_keys (pk{1}, sk{1}) /\
   ! OrPI_bad2.bad{1}).
inline OrPI_bad2.init PI_bad_ub.Or.init.
auto; smt().
inline OrPI_bad2.check_preimage; wp => /=.
call
  (_ :
   ={pk, sk, cs, ctr}(OrPI_bad2, PI_bad_ub.Or) /\
   ! OrPI_bad2.bad{1} /\
   ((exists c, c \in PI_bad_ub.Or.cs{2} /\
     dec PI_bad_ub.Or.sk{2} c = Some pt_def) =>
    PI_bad_ub.Or.bad{2})).
proc.
if => //.
auto; smt(in_fsetU in_fset1).
auto.
proc; auto.
auto; smt(in_fset0 correctness).
qed.

(* we use the failure event lemma to produce a concrete
   upper bound *)

local lemma PI_bad_ub_concrete &m :
  Pr[PI_bad_ub.main() @ &m : PI_bad_ub.Or.bad] <=
  mu_obliv_enc_dec_exact_ub * runs%r.
proof.
fel
  2
  PI_bad_ub.Or.ctr
  (fun n => mu_obliv_enc_dec_exact_ub)
  runs
  PI_bad_ub.Or.bad
  [PI_bad_ub.Or.obliv : (PI_bad_ub.Or.ctr < runs);
   PI_bad_ub.Or.dec : false]
  (PI_bad_ub.Or.ctr <= runs /\
   valid_keys (PI_bad_ub.Or.pk, PI_bad_ub.Or.sk)).
(* sum <= bound *)
rewrite sumr_const intmulr count_predT size_range /=.
by rewrite IntOrder.ler_maxr 1:ge0_runs.
(* invariant good *)
trivial.
(* initialization *)
inline*; auto; smt(ge0_runs).
(* obliv bad set prob *)
proc.
if.
wp.
rnd
  (fun r =>
     dec PI_bad_ub.Or.sk (obliv_enc PI_bad_ub.Or.pk r) = Some pt_def).
skip; progress.
by apply mu_obliv_enc_dec_exact_ub.
smt().
auto.
(* obliv precondition true, preservation *)
move => c; proc.
rcondt 1; first auto.
auto; smt().
(* obliv precondition false, preservation *)
move => b c; proc.
rcondf 1; first auto.
auto.
qed.

local lemma PreImage_AdvPI_PI_bad2_ub &m :
  `|Pr[PreImage(AdvPI).main() @ &m : res] -
    Pr[PI_bad2.main() @ &m : res]| <=
    mu_obliv_enc_dec_exact_ub * runs%r.
proof.
rewrite (ler_trans Pr[PI_bad2.main() @ &m : OrPI_bad2.bad]).
rewrite (PreImage_AdvPI_PI_bad2 &m).
rewrite (ler_trans Pr[PI_bad_ub.main() @ &m : PI_bad_ub.Or.bad]).
rewrite (PI_bad2_ub &m).
rewrite (PI_bad_ub_concrete &m).
qed.

local lemma PI_bad2_IndCCA2_AdvPI2IndCCAAdv_AdvPI &m :
  Pr[PI_bad2.main() @ &m : res] =
  Pr[IndCCA2(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res].
proof.
byequiv => //.
proc.
seq 2 2 : 
  (={pk, sk, glob AdvPI} /\
   ={pk, sk, cs, ctr}(OrPI_bad2, OrIndCCA2) /\
   pk{1} = OrPI_bad2.pk{1} /\ OrPI_bad2.cs{1} = fset0 /\
   OrPI_bad2.ctr{1} = 0).
inline*; auto.
inline*; wp; sp.
call
  (_ :
   ={pk, cs, ctr}(OrPI_bad2, AdvPI2IndCCAAdv.OrPI) /\
   ={pk, sk, cs, ctr}(OrPI_bad2, OrIndCCA2)).
proc; inline*.
if => //.
rcondt{2} 2; first auto.
auto.
auto.
proc.
inline OrIndCCA2.dec.
auto.
auto.
qed.

local lemma IndCCA1_AdvPI2IndCCAAdv_AdvPI_0 &m :
  Pr[IndCCA1(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res] = 0%r.
proof.
byphoare => //; proc; hoare.
seq 2 :
  (pk = OrIndCCA1.pk /\ sk = OrIndCCA1.sk /\ valid_keys (pk, sk) /\
   OrIndCCA1.cs = fset0 /\ OrIndCCA1.ctr = 0).
inline*; auto; smt().
inline*; wp.
seq 6 :
  (AdvPI2IndCCAAdv.OrPI.pk = OrIndCCA1.pk /\
   AdvPI2IndCCAAdv.OrPI.cs = OrIndCCA1.cs /\
   AdvPI2IndCCAAdv.OrPI.ctr = OrIndCCA1.ctr /\
   pk0 = OrIndCCA1.pk /\ valid_keys (OrIndCCA1.pk, OrIndCCA1.sk) /\
   OrIndCCA1.ctr = 0 /\ OrIndCCA1.cs = fset0).
auto.
conseq
  (_ :
   _ ==>
   enc AdvPI2IndCCAAdv.OrPI.pk x r \notin AdvPI2IndCCAAdv.OrPI.cs \/
   x = pt_def).
move => /> &hr _ cs r1 x1.
by rewrite negb_and.
call
  (_ :
   AdvPI2IndCCAAdv.OrPI.pk = OrIndCCA1.pk /\
   AdvPI2IndCCAAdv.OrPI.cs = OrIndCCA1.cs /\
   AdvPI2IndCCAAdv.OrPI.ctr = OrIndCCA1.ctr /\
   valid_keys (OrIndCCA1.pk, OrIndCCA1.sk) /\
   0 <= OrIndCCA1.ctr <= runs /\
   (forall c,
    c \in OrIndCCA1.cs =>
    exists r, c = enc OrIndCCA1.pk pt_def r)).
proc.
if.
wp; inline*.
rcondt 2.
auto.
auto => /> &hr _ ge0_ctr _ H lt_ctr_runs r' _ _ _.
split => [| c']; first smt().
rewrite in_fsetU in_fset1 => [[c'_in_cs | ->]].
by apply H.
by exists r'.
auto.
proc; inline *; auto.
auto => /> &hr vks.
split => [| ge0_runs _].
split => [| c']; first apply ge0_runs.
by rewrite in_fset0.
move => [pt' r'] cs' ctr' _ _ H /=.
case (enc OrIndCCA1.pk{hr} pt' r' \notin cs') => [// | /= enc_pt'_r'_in_cs'].
have [r'' enc_pt'_r'_eq_enc_pt_def_r''] :
  exists (r'' : rand),
  enc OrIndCCA1.pk{hr} pt' r' = enc OrIndCCA1.pk{hr} pt_def r''.
  by apply H.
have A :
  dec OrIndCCA1.sk{hr} (enc OrIndCCA1.pk{hr} pt' r') = Some pt'.
  by apply correctness.
have B :
  dec OrIndCCA1.sk{hr} (enc OrIndCCA1.pk{hr} pt_def r'') = Some pt_def.
  by apply correctness.
rewrite enc_pt'_r'_eq_enc_pt_def_r'' in A.
by rewrite A in B.
qed.

local lemma PI_bad2_0 &m :
  `|Pr[PI_bad2.main() @ &m : res] - 0%r| <=
  `|Pr[IndCCA1(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res] -
    Pr[IndCCA2(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res]|.
proof.
rewrite RealOrder.distrC.
rewrite IndCCA1_AdvPI2IndCCAAdv_AdvPI_0.
by rewrite PI_bad2_IndCCA2_AdvPI2IndCCAAdv_AdvPI.
qed.

lemma PreImage_AdvPI_sec &m :
  Pr[PreImage(AdvPI).main() @ &m : res] <=
  mu_obliv_enc_dec_exact_ub * runs%r +
  `|Pr[IndCCA1(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res] -
    Pr[IndCCA2(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res]|.
proof.
have -> :
  Pr[PreImage(AdvPI).main() @ &m : res] =
  `|Pr[PreImage(AdvPI).main() @ &m : res] - 0%r|.
  by rewrite /= ger0_norm 1:Pr [mu_ge0].
rewrite
  (ler_trans
   (`|Pr[PreImage(AdvPI).main() @ &m : res] -
      Pr[PI_bad2.main() @ &m : res] | +
    `|Pr[PI_bad2.main() @ &m : res] - 0%r|)).
rewrite ler_dist_add.
rewrite ler_add.
rewrite (PreImage_AdvPI_PI_bad2_ub &m).
rewrite (PI_bad2_0 &m).
qed.

end section.

lemma PreImage_AdvPI_security
      (AdvPI <: ADV_PI{-OrPI, -OrIndCCA1, -OrIndCCA2, -AdvPI2IndCCAAdv})
      &m :
  Pr[PreImage(AdvPI).main() @ &m : res] <=
  mu_obliv_enc_dec_exact_ub * runs%r +
  `|Pr[IndCCA1(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res] -
    Pr[IndCCA2(AdvPI2IndCCAAdv(AdvPI)).main() @ &m : res]|.
proof.
apply (PreImage_AdvPI_sec AdvPI &m).
qed.
