(* KeysExponentsAndPlainTexts.ec *)

prover [""].  (* no use of SMT provers *)

require import AllCore Distr.
require import UCBasicTypes.

(********************** Keys, Exponents and Plain texts ***********************)

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)

op kid : key.  (* identity *)

op kinv : key -> key.  (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom kid_l (x : key) : kid ^^ x = x.

axiom kid_r (x : key) : x ^^ kid = x.

axiom kinv_l (x : key) : kinv x ^^ x = kid.

axiom kinv_r (x : key) : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op epdp_exp_univ : (exp, univ) epdp.  (* EPDP from exp to univ *)

axiom valid_epdp_exp_univ : valid_epdp epdp_exp_univ.

hint simplify [eqtrue] valid_epdp_exp_univ.
hint rewrite epdp : valid_epdp_exp_univ. 

(* full (every element has non-zero weight), uniform (all elements
   with non-zero weight have same weight) and lossless (sum of all
   weights is 1%r) distribution over exp

   consequently exp has only finitely many elements *)

op dexp : exp distr.

axiom dexp_fu  : is_full dexp.
axiom dexp_uni : is_uniform dexp.
axiom dexp_ll  : is_lossless dexp.

hint simplify dexp_ll.  (* so simplify and smt() can use axiom *)

(* connection between key and exp, via generator key and
   exponentiation operation *)

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* the following axioms say that each key is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : key) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(* plain texts, with an EPDP to key *)

type text.

op epdp_text_key : (text, key) epdp.  (* EPDP from text to key *)

axiom valid_epdp_text_key : valid_epdp epdp_text_key.

hint simplify valid_epdp_text_key.

(* consequences of axioms *)

(* if a bug in simplification hints is fixed, we won't need
   the following lemma and hint *)

lemma epdp_text_key_cancel (t : text) :
  epdp_text_key.`dec (epdp_text_key.`enc t) = Some t.
proof.
by rewrite !epdp.
qed.

hint simplify [reduce] epdp_text_key_cancel.

(* common simplifications needed in security proofs suitable
   for use in automated rewriting: *)

lemma one_time1 (x y : key) :
  x ^^ y ^^ kinv y = x.
proof.
by rewrite kmulA kinv_r kid_r.
qed.

(* so simplify and smt() can use right-to-left equation *)

hint simplify [reduce] one_time1.

(* we can define a bijection between exp and key *)

op gen (q : exp) : key = g ^ q.

op gen_rel (x : key) (q : exp) : bool = x = g ^ q.

op log (x : key) : exp = choiceb (gen_rel x) e.

lemma gen_log : cancel gen log.
proof.
rewrite /gen /log /cancel => q.
have choice_g2q := choicebP (gen_rel (g ^ q)) e.
have /choice_g2q @/gen_rel /gen_inj {2}-> // :
  exists (q' : exp), gen_rel (g ^ q) q'
  by rewrite /gen_rel; by exists q.
qed.

lemma log_gen : cancel log gen.
proof.
rewrite /gen /log /cancel => x.
have @/gen_rel <- // := choicebP (gen_rel x) e.
rewrite gen_surj.
qed.

lemma double_exp (x : key, q1 q2 : exp) :
  (x ^ q1) ^ q2 = x ^ (q1 * q2).
proof.
have -> : x = g ^ log x.
  by rewrite -/(gen (log x)) log_gen.
by rewrite !double_exp_gen mulA.
qed.

(* EPDP from key to univ *)

op epdp_key_univ : (key, univ) epdp =
  epdp_comp epdp_exp_univ (epdp_bijection log gen).

lemma valid_epdp_key_univ : valid_epdp epdp_key_univ.
proof.
rewrite valid_epdp_comp !(epdp, epdp_sub) 1:log_gen gen_log.
qed.

hint simplify valid_epdp_key_univ.

(* if a bug in simplification hints is fixed, we won't need
   the following lemma and hint *)

lemma epdp_key_univ_cancel (k : key) :
  epdp_key_univ.`dec (epdp_key_univ.`enc k) = Some k.
proof.
by rewrite !epdp.
qed.

hint simplify [reduce] epdp_key_univ_cancel.

(* EPDP from text to univ *)

op epdp_text_univ : (text, univ) epdp =
  epdp_comp epdp_key_univ epdp_text_key.

lemma valid_epdp_text_univ : valid_epdp epdp_text_univ.
proof.
rewrite valid_epdp_comp epdp.
qed.

hint simplify valid_epdp_text_univ.

(* if a bug in simplification hints is fixed, we won't need
   the following lemma and hint *)

lemma epdp_text_univ_cancel (t : text) :
  epdp_text_univ.`dec (epdp_text_univ.`enc t) = Some t.
proof.
by rewrite !epdp.
qed.

hint simplify [reduce] epdp_text_univ_cancel.

(* EPDP between port * port * key and univ *)

op nosmt epdp_port_port_key_univ : (port * port * key, univ) epdp =
  epdp_tuple3_univ epdp_port_univ epdp_port_univ epdp_key_univ.

lemma valid_epdp_port_port_key_univ :
  valid_epdp epdp_port_port_key_univ.
proof.
rewrite valid_epdp_comp !(epdp, epdp_sub).
qed.

hint simplify valid_epdp_port_port_key_univ.

(* if a bug in simplification hints is fixed, we won't need
   the following lemma and hint *)

lemma epdp_port_port_key_univ_cancel (x : port * port * key) :
  epdp_port_port_key_univ.`dec (epdp_port_port_key_univ.`enc x) = Some x.
proof.
by rewrite !epdp.
qed.

hint simplify [reduce] epdp_port_port_key_univ_cancel.

(*added for tests*)
theory T.
op addr_x : addr.
op port_x : port.
op port_y : port.
op testtext : text.
end T.

op testaddr : addr = [1].

op dinttrip : (int * int * int) distr.

type foo = [
  | A of int & bool
  | B of (int * bool)
].

print A.
(* op A : int -> bool -> foo = < 1-th constructor of foo >. *)

print B.
(* op B : int * bool -> foo = < 2-th constructor of foo >. *)

(* so A and B have different types *)

print get_as_A.
(*
op get_as_A (_ : foo) : foo -> (int * bool) option =
  fun (the0 : foo) =>
    match the0 with | A (i, b) => Some (i, b) | B x => None end.
*)

print get_as_B.
(*
op get_as_B (_ : foo) : foo -> (int * bool) option =
  fun (the0 : foo) => match the0 with | A (i, b) => None | B x => Some x end.
*)

(* so get_as_A and get_as_B have identical types *)

op a = get_as_A (A 1 false).

lemma lem_a : a = Some (1, false).
proof. rewrite /a /get_as_A //. qed.

op b = get_as_B (B (1, false)).

lemma lem_b : b = Some (1, false).
proof. rewrite /b /get_as_B //. qed.

(* deconstruction doesn't need to return the full path for the
   constructor - just the basename is fine, as that's all that's
   left in the clauses of the match

   but your deconstruction function needs to return a value of
   type

   symbol * form list

   the value (A 1 false) will turn into ("A", [1; false]) -- two forms

   the value (B (1, false)) will turn into ("B", [(1, false)]) -- one form

   with matching:

   match A 1 false with
   | A n b => { ... }   -- n gets bound to 1, b to false
   | B p   => { ... }

   here your function returns ("A", [1; false]), so there
   are two element to be bound to the two identifers

   match B (1, false) with
   | A n b => { ... }
   | B p   => { ... }   -- p gets bound to (1, false)

   here your function returns ("B", [(1, false)]), so there
   is just one idenfier to bind to the single element of the list *)
