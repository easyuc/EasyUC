(* Encoding.ec *)

(* Encoding and Partial Decoding *)

prover ["Alt-Ergo" "Z3"].

require import AllCore.

(* encoding/partial decoding pair *)

pred epdp (enc : 'a -> 'b, dec : 'b -> 'a option) =
  (forall (x : 'a), dec(enc x) = Some x) /\
  (forall (y : 'b, x : 'a), dec y = Some x => enc x = y).

lemma epdp_injective (enc : 'a -> 'b, dec : 'b -> 'a option) :
  epdp enc dec => injective enc.
proof.
rewrite /epdp => [[epdp_inj_proj1 _]].
by rewrite (pcan_inj enc dec).
qed.

(* turn a partial decoding operator into a validity test *)

op dec2valid (dec : 'b -> 'a option, y : 'b) : bool = dec y <> None.

lemma epdp_intro (enc : 'a -> 'b, dec : 'b -> 'a option) :
  (forall (x : 'a), dec(enc x) = Some x) =>
  (forall (y : 'b, x : 'a), dec y = Some x => enc x = y) =>
  epdp enc dec.
proof.
trivial.
qed.

lemma epdp_dec2valid_enc (enc : 'a -> 'b, dec : 'b -> 'a option, x : 'a) :
  epdp enc dec => dec2valid dec (enc x).
proof.
rewrite /epdp /dec2valid /#.
qed.

lemma epdp_enc_dec (enc : 'a -> 'b, dec : 'b -> 'a option, x : 'a) :
  epdp enc dec => dec (enc x) = Some x.
proof.
smt().
qed.

lemma epdp_dec_enc (enc : 'a -> 'b, dec : 'b -> 'a option, x : 'a, y : 'b) :
  epdp enc dec => dec y = Some x => enc x = y.
proof.
smt().
qed.

abstract theory EPDP.

type orig, enc.

op enc : orig -> enc.

op dec : enc -> orig option.

axiom epdp : epdp enc dec.

op valid = dec2valid dec.

lemma valid_enc (x : orig) : valid (enc x).
proof.
rewrite /valid epdp_dec2valid_enc epdp.
qed.

lemma enc_dec (x : orig) : dec (enc x) = Some x.
proof.
apply /epdp_enc_dec /epdp.
qed.

hint simplify enc_dec.

lemma dec_enc (x : orig, y : enc) :
  dec y = Some x => enc x = y.
proof.
apply /epdp_dec_enc /epdp.
qed.

end EPDP.
