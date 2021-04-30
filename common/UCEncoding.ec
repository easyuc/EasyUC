(* Encoding.ec *)

(* Encoding and Partial Decoding Pairs *)

prover [""].  (* no use of SMT provers *)

require import AllCore List.

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

(* epdp is used for EPDP rewriting hints that generate no subgoals *)

hint rewrite epdp : epdp_enc_dec.

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

hint simplify [eqtrue] valid_epdp_id.
hint rewrite epdp : valid_epdp_id.

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

(* epdp_sub is used for EPDP rewriting hints that generate subgoals *)

hint rewrite epdp_sub : valid_epdp_bijection.

(* composition of EPDPs *)

op nosmt epdp_comp
     (epdp2 : ('b, 'c) epdp, epdp1 : ('a, 'b) epdp) : ('a, 'c) epdp =
  {|enc = (\o) epdp2.`enc epdp1.`enc;
    dec =
      fun z =>
        match epdp2.`dec z with
        | None   => None
        | Some y => epdp1.`dec y
        end|}.

lemma valid_epdp_comp (epdp2 : ('b, 'c) epdp, epdp1 : ('a, 'b) epdp) :
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

(* pair EPDPs *)

op nosmt epdp_pair_enc
     (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp,
      p : 'a * 'b) : 'c * 'd =
  (epdp1.`enc p.`1, epdp2.`enc p.`2).

op nosmt epdp_pair_dec
     (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp,
      p : 'c * 'd) : ('a * 'b) option =
  match epdp1.`dec p.`1 with
  | None   => None
  | Some a =>
      match epdp2.`dec p.`2 with
      | None   => None
      | Some b => Some (a, b)
      end
  end.

op nosmt epdp_pair
     (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp) :
      ('a * 'b, 'c * 'd) epdp =
  {|enc = epdp_pair_enc epdp1 epdp2;
    dec = epdp_pair_dec epdp1 epdp2|}.

lemma valid_epdp_pair (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 =>
  valid_epdp (epdp_pair epdp1 epdp2).
proof.
move => valid1 valid2.
rewrite epdp_intro => [x | a b].
rewrite /epdp_pair /epdp_pair_enc /epdp_pair_dec /=.
rewrite epdp_enc_dec //= epdp_enc_dec //=.
by case x.
rewrite /epdp_pair /epdp_pair_enc /epdp_pair_dec /= => match_some.
have val_a1 : epdp1.`dec a.`1 = Some b.`1.
  move : match_some.
  case (epdp1.`dec a.`1) => [// | x /=].
  case (epdp2.`dec a.`2) => [// | y /= <- //].
move : match_some.
rewrite val_a1 /=.
move => match_some.
have val_a2 : epdp2.`dec a.`2 = Some b.`2.
  move : match_some.
  case (epdp2.`dec a.`2) => [// | x /= <- //].
rewrite (epdp_dec_enc _ _ a.`1) //.
rewrite (epdp_dec_enc _ _ a.`2) //.
clear val_a1 val_a2 match_some.
by case a.
qed.

hint rewrite epdp_sub : valid_epdp_pair.

(* triple EPDPs *)

op triple_decon (x : 'a * 'b * 'c) : 'a * ('b * 'c) =
  (x.`1, (x.`2, x.`3)).

op triple_con (x : 'a * ('b * 'c)) : 'a * 'b * 'c =
  (x.`1, x.`2.`1, x.`2.`2).

lemma triple_deconK (x : 'a * 'b * 'c) :
  triple_con (triple_decon x) = x.
proof.
rewrite /triple_con /triple_decon.
by case x.
qed.

lemma triple_conK (x : 'a * ('b * 'c)) :
  triple_decon (triple_con x) = x.
proof.
rewrite /triple_con /triple_decon.
case x => /= [[x1 x2] //].
qed.

op nosmt epdp_triple
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp) :
       ('a * 'b * 'c, 'a' * 'b' * 'c') epdp =
  epdp_comp
  (epdp_bijection triple_con triple_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_pair epdp2 epdp3))
   (epdp_bijection triple_decon triple_con)).

lemma valid_epdp_triple
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp (epdp_triple epdp1 epdp2 epdp3).
proof.
move => valid1 valid2 valid3.
rewrite valid_epdp_comp 1:epdp_sub.
move => x; by rewrite triple_conK.
move => x; by rewrite triple_deconK.
rewrite valid_epdp_comp epdp_sub // 1:epdp_sub //.
move => x; by rewrite triple_deconK.
move => x; by rewrite triple_conK.
qed.

hint rewrite epdp_sub : valid_epdp_triple.

(* quadruple EPDPs *)

op quadruple_decon (x : 'a * 'b * 'c * 'd) : 'a * ('b * 'c * 'd) =
  (x.`1, (x.`2, x.`3, x.`4)).

op quadruple_con (x : 'a * ('b * 'c * 'd)) : 'a * 'b * 'c * 'd =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3).

lemma quadruple_deconK (x : 'a * 'b * 'c * 'd) :
  quadruple_con (quadruple_decon x) = x.
proof.
rewrite /quadruple_con /quadruple_decon.
by case x.
qed.

lemma quadruple_conK (x : 'a * ('b * 'c * 'd)) :
  quadruple_decon (quadruple_con x) = x.
proof.
rewrite /quadruple_con /quadruple_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_quadruple
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp) :
       ('a * 'b * 'c * 'd, 'a' * 'b' * 'c' * 'd') epdp =
  epdp_comp
  (epdp_bijection quadruple_con quadruple_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_triple epdp2 epdp3 epdp4))
   (epdp_bijection quadruple_decon quadruple_con)).

lemma valid_epdp_quadruple
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 =>
  valid_epdp (epdp_quadruple epdp1 epdp2 epdp3 epdp4).
proof.
move => valid1 valid2 valid3 valid4.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite quadruple_conK.
move => x; by rewrite quadruple_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_triple //.
rewrite valid_epdp_bijection.
move => x; by rewrite quadruple_deconK.
move => x; by rewrite quadruple_conK.
qed.

hint rewrite epdp_sub : valid_epdp_quadruple.

(* quintuple EPDPs *)

op quintuple_decon (x : 'a * 'b * 'c * 'd * 'e) : 'a * ('b * 'c * 'd * 'e) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5)).

op quintuple_con (x : 'a * ('b * 'c * 'd * 'e)) : 'a * 'b * 'c * 'd * 'e =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4).

lemma quintuple_deconK (x : 'a * 'b * 'c * 'd * 'e) :
  quintuple_con (quintuple_decon x) = x.
proof.
rewrite /quintuple_con /quintuple_decon.
by case x.
qed.

lemma quintuple_conK (x : 'a * ('b * 'c * 'd * 'e)) :
  quintuple_decon (quintuple_con x) = x.
proof.
rewrite /quintuple_con /quintuple_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_quintuple
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp) :
       ('a * 'b * 'c * 'd * 'e, 'a' * 'b' * 'c' * 'd' * 'e') epdp =
  epdp_comp
  (epdp_bijection quintuple_con quintuple_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_quadruple epdp2 epdp3 epdp4 epdp5))
   (epdp_bijection quintuple_decon quintuple_con)).

lemma valid_epdp_quintuple
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 =>
  valid_epdp (epdp_quintuple epdp1 epdp2 epdp3 epdp4 epdp5).
proof.
move => valid1 valid2 valid3 valid4 valid5.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite quintuple_conK.
move => x; by rewrite quintuple_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_quadruple //.
rewrite valid_epdp_bijection.
move => x; by rewrite quintuple_deconK.
move => x; by rewrite quintuple_conK.
qed.

hint rewrite epdp_sub : valid_epdp_quintuple.

(* sextuple EPDPs *)

op sextuple_decon
   (x : 'a * 'b * 'c * 'd * 'e * 'f) : 'a * ('b * 'c * 'd * 'e * 'f) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5, x.`6)).

op sextuple_con
   (x : 'a * ('b * 'c * 'd * 'e * 'f)) : 'a * 'b * 'c * 'd * 'e * 'f =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4, x.`2.`5).

lemma sextuple_deconK (x : 'a * 'b * 'c * 'd * 'e * 'f) :
  sextuple_con (sextuple_decon x) = x.
proof.
rewrite /sextuple_con /sextuple_decon.
by case x.
qed.

lemma sextuple_conK (x : 'a * ('b * 'c * 'd * 'e * 'f)) :
  sextuple_decon (sextuple_con x) = x.
proof.
rewrite /sextuple_con /sextuple_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_sextuple
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp) :
       ('a * 'b * 'c * 'd * 'e * 'f,
        'a' * 'b' * 'c' * 'd' * 'e' * 'f') epdp =
  epdp_comp
  (epdp_bijection sextuple_con sextuple_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_quintuple epdp2 epdp3 epdp4 epdp5 epdp6))
   (epdp_bijection sextuple_decon sextuple_con)).

lemma valid_epdp_sextuple
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp (epdp_sextuple epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite sextuple_conK.
move => x; by rewrite sextuple_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_quintuple //.
rewrite valid_epdp_bijection.
move => x; by rewrite sextuple_deconK.
move => x; by rewrite sextuple_conK.
qed.

hint rewrite epdp_sub : valid_epdp_sextuple.

(* septuple EPDPs *)

op septuple_decon
   (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g)
     : 'a * ('b * 'c * 'd * 'e * 'f * 'g) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7)).

op septuple_con
   (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g))
     : 'a * 'b * 'c * 'd * 'e * 'f * 'g =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4, x.`2.`5, x.`2.`6).

lemma septuple_deconK (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g) :
  septuple_con (septuple_decon x) = x.
proof.
rewrite /septuple_con /septuple_decon.
by case x.
qed.

lemma septuple_conK (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g)) :
  septuple_decon (septuple_con x) = x.
proof.
rewrite /septuple_con /septuple_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_septuple
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp) :
       ('a * 'b * 'c * 'd * 'e * 'f * 'g,
        'a' * 'b' * 'c' * 'd' * 'e' * 'f' * 'g') epdp =
  epdp_comp
  (epdp_bijection septuple_con septuple_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_sextuple epdp2 epdp3 epdp4 epdp5 epdp6 epdp7))
   (epdp_bijection septuple_decon septuple_con)).

lemma valid_epdp_septuple
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
       epdp7 : ('g, 'g') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 =>
  valid_epdp (epdp_septuple epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite septuple_conK.
move => x; by rewrite septuple_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_sextuple //.
rewrite valid_epdp_bijection.
move => x; by rewrite septuple_deconK.
move => x; by rewrite septuple_conK.
qed.

hint rewrite epdp_sub : valid_epdp_septuple.

(* octuple EPDPs *)

op octuple_decon
   (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h)
     : 'a * ('b * 'c * 'd * 'e * 'f * 'g * 'h) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7, x.`8)).

op octuple_con
   (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g * 'h))
     : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4, x.`2.`5, x.`2.`6, x.`2.`7).

lemma octuple_deconK (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h) :
  octuple_con (octuple_decon x) = x.
proof.
rewrite /octuple_con /octuple_decon.
by case x.
qed.

lemma octuple_conK (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g * 'h)) :
  octuple_decon (octuple_con x) = x.
proof.
rewrite /octuple_con /octuple_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_octuple
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp) :
       ('a * 'b * 'c * 'd * 'e * 'f * 'g * 'h,
        'a' * 'b' * 'c' * 'd' * 'e' * 'f' * 'g' * 'h') epdp =
  epdp_comp
  (epdp_bijection octuple_con octuple_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_septuple epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8))
   (epdp_bijection octuple_decon octuple_con)).

lemma valid_epdp_octuple
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
       epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 => valid_epdp epdp8 =>
  valid_epdp (epdp_octuple epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7 valid8.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite octuple_conK.
move => x; by rewrite octuple_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_septuple //.
rewrite valid_epdp_bijection.
move => x; by rewrite octuple_deconK.
move => x; by rewrite octuple_conK.
qed.

hint rewrite epdp_sub : valid_epdp_octuple.

(* choice EPDPs *)

type ('a, 'b) choice = [
  | ChoiceLeft  of 'a
  | ChoiceRight of 'b
].

op nosmt epdp_choice_enc
     (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp,
      ch : ('a, 'b) choice) : ('c, 'd) choice =
  match ch with
  | ChoiceLeft x  => ChoiceLeft (epdp1.`enc x)
  | ChoiceRight x => ChoiceRight (epdp2.`enc x)
  end.

op nosmt epdp_choice_dec
     (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp,
      ch : ('c, 'd) choice) : ('a, 'b) choice option =
  match ch with
  | ChoiceLeft x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (ChoiceLeft y)
      end
  | ChoiceRight x =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (ChoiceRight y)
      end
  end.

op nosmt epdp_choice
     (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp) :
     (('a, 'b) choice, ('c, 'd) choice) epdp =
  {|enc = epdp_choice_enc epdp1 epdp2;
    dec = epdp_choice_dec epdp1 epdp2|}.

lemma valid_epdp_choice (epdp1 : ('a, 'c) epdp, epdp2 : ('b, 'd) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 =>
  valid_epdp (epdp_choice epdp1 epdp2).
proof.
move => valid1 valid2.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice /epdp_choice_enc /epdp_choice_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice /epdp_choice_enc /epdp_choice_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice.

(* option EPDPs *)

op opt_to_unit_choice (opt : 'a option) : (unit, 'a) choice =
  match opt with
  | None   => ChoiceLeft ()
  | Some x => ChoiceRight x
  end.

op unit_choice_to_opt (ch : (unit, 'a) choice) : 'a option =
  match ch with
  | ChoiceLeft _  => None
  | ChoiceRight x => Some x
  end.

lemma opt_to_unit_choiceK (opt : 'a option) :
  unit_choice_to_opt (opt_to_unit_choice opt) = opt.
proof.
rewrite /unit_choice_to_opt /opt_to_unit_choice.
by case opt.
qed.

lemma unit_choice_to_optK (ch : (unit, 'a) choice) :
  opt_to_unit_choice (unit_choice_to_opt ch) = ch.
proof.
rewrite /unit_choice_to_opt /opt_to_unit_choice.
by case ch.
qed.

op epdp_opt_unit_choice : ('a option, (unit, 'a) choice) epdp =
  epdp_bijection opt_to_unit_choice unit_choice_to_opt.

lemma valid_epdp_opt_unit_choice :
  valid_epdp epdp_opt_unit_choice<:'a>.
proof.
rewrite /epdp_opt_unit_choice valid_epdp_bijection => opt.
by rewrite opt_to_unit_choiceK.
by rewrite unit_choice_to_optK.
qed.

op epdp_unit_choice_opt : ((unit, 'a) choice, 'a option) epdp =
  epdp_bijection unit_choice_to_opt opt_to_unit_choice.

lemma valid_epdp_unit_choice_opt :
  valid_epdp epdp_unit_choice_opt<:'a>.
proof.
rewrite /epdp_opt_unit_choice valid_epdp_bijection => opt.
by rewrite unit_choice_to_optK.
by rewrite opt_to_unit_choiceK.
qed.

op nosmt epdp_option
     (epdp : ('a, 'b) epdp) : ('a option, 'b option) epdp =
  epdp_comp epdp_unit_choice_opt
  (epdp_comp (epdp_choice epdp_id epdp) epdp_opt_unit_choice).

lemma valid_epdp_option (epdp : ('a, 'b) epdp) :
  valid_epdp epdp => valid_epdp (epdp_option epdp).
proof.
move => valid.
rewrite /epdp_option valid_epdp_comp 1:valid_epdp_unit_choice_opt
        valid_epdp_comp 1:valid_epdp_choice 1:valid_epdp_id //
        valid_epdp_opt_unit_choice.
qed.

hint rewrite epdp_sub : valid_epdp_option.

(* list EPDPs *)

op nosmt epdp_list_enc (epdp : ('a, 'b) epdp, xs : 'a list) : 'b list =
  map epdp.`enc xs.

op nosmt epdp_list_dec
     (epdp : ('a, 'b) epdp, ys : 'b list) : 'a list option =
  let vs = map epdp.`dec ys
  in if all is_some vs
     then Some (map oget vs)
     else None.

op nosmt epdp_list (epdp : ('a, 'b) epdp) : ('a list, 'b list) epdp =
  {|enc = epdp_list_enc epdp; dec = epdp_list_dec epdp|}.

lemma valid_epdp_list (epdp : ('a, 'b) epdp) :
  valid_epdp epdp => valid_epdp (epdp_list epdp).
proof.  
move => valid.
apply epdp_intro => [xs | ys xs].
rewrite /epdp_list /epdp_list_enc /epdp_list_dec /=.
have -> : map epdp.`dec (map epdp.`enc xs) = map Some xs.
  elim xs => [// | y ys /=].
  rewrite !epdp //.
have -> /= : all is_some (map Some xs) = true.
  elim xs => [// | y ys //].
elim xs => [// | y ys //].
rewrite /epdp_list /epdp_list_enc /epdp_list_dec /=.
case (all is_some (map epdp.`dec ys)) => [/= | //].
move : xs.
elim ys => [// | y ys IH xs /= [is_some_dec_y all_is_some_dec_ys <- /=]].
split.
rewrite (epdp_dec_enc _ _ y) // -some_oget //.
case (epdp.`dec y = None) => [dec_y_eq_None | //].
move : is_some_dec_y.
by rewrite dec_y_eq_None.
by apply IH.
qed.

hint rewrite epdp_sub : valid_epdp_list.
