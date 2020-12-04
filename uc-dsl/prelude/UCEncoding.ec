(* Encoding.ec *)

(* Encoding and Partial Decoding Pairs *)

prover [""].  (* no use of SMT provers *)

require import AllCore.

(* encoding/partial decoding pair (EPDP) *)

type ('a, 'b) epdp = {enc: 'a -> 'b; dec : 'b -> 'a option}.

op nosmt valid_epdp (epdp : ('a, 'b) epdp) : bool =
  (forall (x : 'a), epdp.`dec (epdp.`enc x) = Some x) /\
  (forall (y : 'b, x : 'a), epdp.`dec y = Some x => epdp.`enc x = y).

(* encoding functions of EPDPs are injective: *)

lemma epdp_injective (epdp : ('a, 'b) epdp) :
  valid_epdp epdp => injective epdp.`enc.
proof.
rewrite /valid_epdp => [[enc_dec _]].
by rewrite (pcan_inj epdp.`enc epdp.`dec).
qed.

(* if a value of an EPDP fails to decode, then nothing will encode to
   it: *)

lemma epdp_dec_fail (epdp : ('a, 'b) epdp, x : 'a, y : 'b) :
  valid_epdp epdp => epdp.`dec y = None => epdp.`enc x <> y.
proof.
move => [valid_epdp_1 valid_epdp_2] dec_y_bad.
case (epdp.`enc x = y) => [enc_x_eq_y | //].
move : dec_y_bad.
by rewrite -enc_x_eq_y valid_epdp_1.
qed.

lemma epdp_intro (epdp : ('a, 'b) epdp) :
  (forall (x : 'a), epdp.`dec (epdp.`enc x) = Some x) =>
  (forall (y : 'b, x : 'a), epdp.`dec y = Some x => epdp.`enc x = y) =>
  valid_epdp epdp.
proof.
trivial.
qed.

(* is_valid epdp y checks whether y decodes in epdp *)

op is_valid (epdp : ('a, 'b) epdp, y : 'b) : bool =
  epdp.`dec y <> None.

lemma is_valid_enc (epdp : ('a, 'b) epdp, x : 'a) :
  valid_epdp epdp => is_valid epdp (epdp.`enc x).
proof.
move => [enc_dec _].
by rewrite /is_valid enc_dec.
qed.

lemma epdp_enc_dec (epdp : ('a, 'b) epdp, x : 'a) :
  valid_epdp epdp => epdp.`dec (epdp.`enc x) = Some x.
proof.
rewrite /valid_epdp => [[enc_dec _]].
by rewrite enc_dec.
qed.

lemma epdp_dec_enc (epdp : ('a, 'b) epdp, x : 'a, y : 'b) :
  valid_epdp epdp => epdp.`dec y = Some x => epdp.`enc x = y.
proof.
rewrite /valid_epdp => [[_ dec_enc]].
move => dec_some.
by rewrite (dec_enc y).
qed.

(* identity EPDP *)

op nosmt epdp_id : ('a, 'a) epdp =
  {|enc = fun x => x; dec = fun y => Some y|}.

lemma valid_epdp_id : valid_epdp epdp_id<:'a>.
proof.
rewrite /valid_epdp /epdp_id /= => y x -> //.
qed.

(* EPDP built from a bijection *)

op nosmt epdp_bijection (f : 'a -> 'b, g : 'b -> 'a) : ('a, 'b) epdp =
  {|enc = f; dec = (\o) Some g|}.

lemma valid_epdp_bijection (f : 'a -> 'b, g : 'b -> 'a) :
  cancel f g => cancel g f => valid_epdp (epdp_bijection f g).
proof.
move => cancel_fg cancel_gf.
rewrite /valid_epdp /epdp_bijection /=.
split => [x | y x].
rewrite /(\o).
congr; apply cancel_fg.
rewrite /(\o) => /= <-.
apply cancel_gf.
qed.

(* composition of EPDPs *)

op nosmt epdp_comp
     (epdp2 : ('b, 'c) epdp) (epdp1 : ('a, 'b) epdp) : ('a, 'c) epdp =
  {|enc = (\o) epdp2.`enc epdp1.`enc;
    dec =
      fun z =>
        match epdp2.`dec z with
        | None   => None
        | Some y => epdp1.`dec y
        end|}.

lemma valid_epdp_comp (epdp2 : ('b, 'c) epdp) (epdp1 : ('a, 'b) epdp) :
  valid_epdp epdp2 => valid_epdp epdp1 =>
  valid_epdp (epdp_comp epdp2 epdp1).
proof.
move => valid2 valid1.
rewrite /valid_epdp /epdp_comp /(\o) /=.
split => [x | y x match_eq_some].
by rewrite epdp_enc_dec //= epdp_enc_dec.
have val_y : epdp2.`dec y = Some (epdp1.`enc x).
  move : match_eq_some.
  case (epdp2.`dec y) => //= x0 val_x0.
  rewrite (epdp_dec_enc _ _ x0) //.
by rewrite (epdp_dec_enc _ _ y).
qed.
