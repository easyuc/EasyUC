(* Encoding.ec *)

(* Encoding and Partial Decoding *)

require import AllCore.

(* encoding/partial decoding pair *)

type ('a, 'b) epdp = {enc: 'a -> 'b; dec : 'b -> 'a option}.

op nosmt valid_epdp (epdp : ('a, 'b) epdp) : bool =
  (forall (x : 'a), epdp.`dec (epdp.`enc x) = Some x) /\
  (forall (y : 'b, x : 'a), epdp.`dec y = Some x => epdp.`enc x = y).

lemma epdp_injective (epdp : ('a, 'b) epdp) :
  valid_epdp epdp => injective epdp.`enc.
proof.
rewrite /valid_epdp => [[enc_dec _]].
by rewrite (pcan_inj epdp.`enc epdp.`dec).
qed.

op is_valid (epdp : ('a, 'b) epdp, y : 'b) : bool =
  epdp.`dec y <> None.

lemma epdp_intro (epdp : ('a, 'b) epdp) :
  (forall (x : 'a), epdp.`dec (epdp.`enc x) = Some x) =>
  (forall (y : 'b, x : 'a), epdp.`dec y = Some x => epdp.`enc x = y) =>
  valid_epdp epdp.
proof.
trivial.
qed.

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
