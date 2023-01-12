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

(* epdp is used for EPDP rewriting hints that generate no subgoals,
   except the validity of an epdp *)

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

(* tuple3 EPDPs *)

op tuple3_decon (x : 'a * 'b * 'c) : 'a * ('b * 'c) =
  (x.`1, (x.`2, x.`3)).

op tuple3_con (x : 'a * ('b * 'c)) : 'a * 'b * 'c =
  (x.`1, x.`2.`1, x.`2.`2).

lemma tuple3_deconK (x : 'a * 'b * 'c) :
  tuple3_con (tuple3_decon x) = x.
proof.
rewrite /tuple3_con /tuple3_decon.
by case x.
qed.

lemma tuple3_conK (x : 'a * ('b * 'c)) :
  tuple3_decon (tuple3_con x) = x.
proof.
rewrite /tuple3_con /tuple3_decon.
case x => /= [[x1 x2] //].
qed.

op nosmt epdp_tuple3
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp) :
       ('a * 'b * 'c, 'a' * 'b' * 'c') epdp =
  epdp_comp
  (epdp_bijection tuple3_con tuple3_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_pair epdp2 epdp3))
   (epdp_bijection tuple3_decon tuple3_con)).

lemma valid_epdp_tuple3
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp (epdp_tuple3 epdp1 epdp2 epdp3).
proof.
move => valid1 valid2 valid3.
rewrite valid_epdp_comp 1:epdp_sub.
move => x; by rewrite tuple3_conK.
move => x; by rewrite tuple3_deconK.
rewrite valid_epdp_comp epdp_sub // 1:epdp_sub //.
move => x; by rewrite tuple3_deconK.
move => x; by rewrite tuple3_conK.
qed.

hint rewrite epdp_sub : valid_epdp_tuple3.

(* tuple4 EPDPs *)

op tuple4_decon (x : 'a * 'b * 'c * 'd) : 'a * ('b * 'c * 'd) =
  (x.`1, (x.`2, x.`3, x.`4)).

op tuple4_con (x : 'a * ('b * 'c * 'd)) : 'a * 'b * 'c * 'd =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3).

lemma tuple4_deconK (x : 'a * 'b * 'c * 'd) :
  tuple4_con (tuple4_decon x) = x.
proof.
rewrite /tuple4_con /tuple4_decon.
by case x.
qed.

lemma tuple4_conK (x : 'a * ('b * 'c * 'd)) :
  tuple4_decon (tuple4_con x) = x.
proof.
rewrite /tuple4_con /tuple4_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_tuple4
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp) :
       ('a * 'b * 'c * 'd, 'a' * 'b' * 'c' * 'd') epdp =
  epdp_comp
  (epdp_bijection tuple4_con tuple4_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_tuple3 epdp2 epdp3 epdp4))
   (epdp_bijection tuple4_decon tuple4_con)).

lemma valid_epdp_tuple4
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 =>
  valid_epdp (epdp_tuple4 epdp1 epdp2 epdp3 epdp4).
proof.
move => valid1 valid2 valid3 valid4.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite tuple4_conK.
move => x; by rewrite tuple4_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_tuple3 //.
rewrite valid_epdp_bijection.
move => x; by rewrite tuple4_deconK.
move => x; by rewrite tuple4_conK.
qed.

hint rewrite epdp_sub : valid_epdp_tuple4.

(* tuple5 EPDPs *)

op tuple5_decon (x : 'a * 'b * 'c * 'd * 'e) : 'a * ('b * 'c * 'd * 'e) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5)).

op tuple5_con (x : 'a * ('b * 'c * 'd * 'e)) : 'a * 'b * 'c * 'd * 'e =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4).

lemma tuple5_deconK (x : 'a * 'b * 'c * 'd * 'e) :
  tuple5_con (tuple5_decon x) = x.
proof.
rewrite /tuple5_con /tuple5_decon.
by case x.
qed.

lemma tuple5_conK (x : 'a * ('b * 'c * 'd * 'e)) :
  tuple5_decon (tuple5_con x) = x.
proof.
rewrite /tuple5_con /tuple5_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_tuple5
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp) :
       ('a * 'b * 'c * 'd * 'e, 'a' * 'b' * 'c' * 'd' * 'e') epdp =
  epdp_comp
  (epdp_bijection tuple5_con tuple5_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_tuple4 epdp2 epdp3 epdp4 epdp5))
   (epdp_bijection tuple5_decon tuple5_con)).

lemma valid_epdp_tuple5
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 =>
  valid_epdp (epdp_tuple5 epdp1 epdp2 epdp3 epdp4 epdp5).
proof.
move => valid1 valid2 valid3 valid4 valid5.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite tuple5_conK.
move => x; by rewrite tuple5_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_tuple4 //.
rewrite valid_epdp_bijection.
move => x; by rewrite tuple5_deconK.
move => x; by rewrite tuple5_conK.
qed.

hint rewrite epdp_sub : valid_epdp_tuple5.

(* tuple6 EPDPs *)

op tuple6_decon
   (x : 'a * 'b * 'c * 'd * 'e * 'f) : 'a * ('b * 'c * 'd * 'e * 'f) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5, x.`6)).

op tuple6_con
   (x : 'a * ('b * 'c * 'd * 'e * 'f)) : 'a * 'b * 'c * 'd * 'e * 'f =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4, x.`2.`5).

lemma tuple6_deconK (x : 'a * 'b * 'c * 'd * 'e * 'f) :
  tuple6_con (tuple6_decon x) = x.
proof.
rewrite /tuple6_con /tuple6_decon.
by case x.
qed.

lemma tuple6_conK (x : 'a * ('b * 'c * 'd * 'e * 'f)) :
  tuple6_decon (tuple6_con x) = x.
proof.
rewrite /tuple6_con /tuple6_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_tuple6
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp) :
       ('a * 'b * 'c * 'd * 'e * 'f,
        'a' * 'b' * 'c' * 'd' * 'e' * 'f') epdp =
  epdp_comp
  (epdp_bijection tuple6_con tuple6_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_tuple5 epdp2 epdp3 epdp4 epdp5 epdp6))
   (epdp_bijection tuple6_decon tuple6_con)).

lemma valid_epdp_tuple6
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp (epdp_tuple6 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite tuple6_conK.
move => x; by rewrite tuple6_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_tuple5 //.
rewrite valid_epdp_bijection.
move => x; by rewrite tuple6_deconK.
move => x; by rewrite tuple6_conK.
qed.

hint rewrite epdp_sub : valid_epdp_tuple6.

(* tuple7 EPDPs *)

op tuple7_decon
   (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g)
     : 'a * ('b * 'c * 'd * 'e * 'f * 'g) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7)).

op tuple7_con
   (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g))
     : 'a * 'b * 'c * 'd * 'e * 'f * 'g =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4, x.`2.`5, x.`2.`6).

lemma tuple7_deconK (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g) :
  tuple7_con (tuple7_decon x) = x.
proof.
rewrite /tuple7_con /tuple7_decon.
by case x.
qed.

lemma tuple7_conK (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g)) :
  tuple7_decon (tuple7_con x) = x.
proof.
rewrite /tuple7_con /tuple7_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_tuple7
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp) :
       ('a * 'b * 'c * 'd * 'e * 'f * 'g,
        'a' * 'b' * 'c' * 'd' * 'e' * 'f' * 'g') epdp =
  epdp_comp
  (epdp_bijection tuple7_con tuple7_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_tuple6 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7))
   (epdp_bijection tuple7_decon tuple7_con)).

lemma valid_epdp_tuple7
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
       epdp7 : ('g, 'g') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 =>
  valid_epdp (epdp_tuple7 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite tuple7_conK.
move => x; by rewrite tuple7_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_tuple6 //.
rewrite valid_epdp_bijection.
move => x; by rewrite tuple7_deconK.
move => x; by rewrite tuple7_conK.
qed.

hint rewrite epdp_sub : valid_epdp_tuple7.

(* tuple8 EPDPs *)

op tuple8_decon
   (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h)
     : 'a * ('b * 'c * 'd * 'e * 'f * 'g * 'h) =
  (x.`1, (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7, x.`8)).

op tuple8_con
   (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g * 'h))
     : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h =
  (x.`1, x.`2.`1, x.`2.`2, x.`2.`3, x.`2.`4, x.`2.`5, x.`2.`6, x.`2.`7).

lemma tuple8_deconK (x : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h) :
  tuple8_con (tuple8_decon x) = x.
proof.
rewrite /tuple8_con /tuple8_decon.
by case x.
qed.

lemma tuple8_conK (x : 'a * ('b * 'c * 'd * 'e * 'f * 'g * 'h)) :
  tuple8_decon (tuple8_con x) = x.
proof.
rewrite /tuple8_con /tuple8_decon.
case x => /= x1.
by case x1.
qed.

op nosmt epdp_tuple8
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp) :
       ('a * 'b * 'c * 'd * 'e * 'f * 'g * 'h,
        'a' * 'b' * 'c' * 'd' * 'e' * 'f' * 'g' * 'h') epdp =
  epdp_comp
  (epdp_bijection tuple8_con tuple8_decon)
  (epdp_comp
   (epdp_pair epdp1 (epdp_tuple7 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8))
   (epdp_bijection tuple8_decon tuple8_con)).

lemma valid_epdp_tuple8
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
       epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 => valid_epdp epdp8 =>
  valid_epdp (epdp_tuple8 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7 valid8.
rewrite valid_epdp_comp 1:valid_epdp_bijection.
move => x; by rewrite tuple8_conK.
move => x; by rewrite tuple8_deconK.
rewrite valid_epdp_comp 1:valid_epdp_pair // 1:valid_epdp_tuple7 //.
rewrite valid_epdp_bijection.
move => x; by rewrite tuple8_deconK.
move => x; by rewrite tuple8_conK.
qed.

hint rewrite epdp_sub : valid_epdp_tuple8.

(* choice EPDPs *)

type ('a, 'b) choice = [
  | ChoiceLeft  of 'a
  | ChoiceRight of 'b
].

op nosmt epdp_choice_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      ch : ('a, 'b) choice) : ('a', 'b') choice =
  match ch with
  | ChoiceLeft x  => ChoiceLeft (epdp1.`enc x)
  | ChoiceRight x => ChoiceRight (epdp2.`enc x)
  end.

op nosmt epdp_choice_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      ch : ('a', 'b') choice) : ('a, 'b) choice option =
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
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp) :
     (('a, 'b) choice, ('a', 'b') choice) epdp =
  {|enc = epdp_choice_enc epdp1 epdp2;
    dec = epdp_choice_dec epdp1 epdp2|}.

lemma valid_epdp_choice
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp) :
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

(* choice3 EPDPs *)

type ('a, 'b, 'c) choice3 = [
  | Choice3_1 of 'a
  | Choice3_2 of 'b
  | Choice3_3 of 'c
].

op nosmt epdp_choice3_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp,
      ch : ('a, 'b, 'c) choice3) : ('a', 'b', 'c') choice3 =
  match ch with
  | Choice3_1 x => Choice3_1 (epdp1.`enc x)
  | Choice3_2 x => Choice3_2 (epdp2.`enc x)
  | Choice3_3 x => Choice3_3 (epdp3.`enc x)
  end.

op nosmt epdp_choice3_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp,
      ch : ('a', 'b', 'c') choice3) : ('a, 'b, 'c) choice3 option =
  match ch with
  | Choice3_1 x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (Choice3_1 y)
      end
  | Choice3_2 x  =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (Choice3_2 y)
      end
  | Choice3_3 x  =>
      match epdp3.`dec x with
      | None   => None
      | Some y => Some (Choice3_3 y)
      end
  end.

op nosmt epdp_choice3
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp) :
     (('a, 'b, 'c) choice3, ('a', 'b', 'c') choice3) epdp =
  {|enc = epdp_choice3_enc epdp1 epdp2 epdp3;
    dec = epdp_choice3_dec epdp1 epdp2 epdp3|}.

lemma valid_epdp_choice3
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp (epdp_choice3 epdp1 epdp2 epdp3).
proof.
move => valid1 valid2 valid3.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice3 /epdp_choice3_enc /epdp_choice3_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice3 /epdp_choice3_enc /epdp_choice3_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp2.`dec x).
case b => y /=.
by case (epdp3.`dec x).
by case (epdp3.`dec x).
move => match_eq_some.
have val_x : epdp3.`dec x = Some y.
  move : match_eq_some.
  by case (epdp3.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice3.

(* choice4 EPDPs *)

type ('a, 'b, 'c, 'd) choice4 = [
  | Choice4_1 of 'a
  | Choice4_2 of 'b
  | Choice4_3 of 'c
  | Choice4_4 of 'd
].

op nosmt epdp_choice4_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      ch : ('a, 'b, 'c, 'd) choice4) : ('a', 'b', 'c', 'd') choice4 =
  match ch with
  | Choice4_1 x => Choice4_1 (epdp1.`enc x)
  | Choice4_2 x => Choice4_2 (epdp2.`enc x)
  | Choice4_3 x => Choice4_3 (epdp3.`enc x)
  | Choice4_4 x => Choice4_4 (epdp4.`enc x)
  end.

op nosmt epdp_choice4_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      ch : ('a', 'b', 'c', 'd') choice4)
       : ('a, 'b, 'c, 'd) choice4 option =
  match ch with
  | Choice4_1 x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (Choice4_1 y)
      end
  | Choice4_2 x  =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (Choice4_2 y)
      end
  | Choice4_3 x  =>
      match epdp3.`dec x with
      | None   => None
      | Some y => Some (Choice4_3 y)
      end
  | Choice4_4 x  =>
      match epdp4.`dec x with
      | None   => None
      | Some y => Some (Choice4_4 y)
      end
  end.

op nosmt epdp_choice4
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp) :
     (('a, 'b, 'c, 'd) choice4, ('a', 'b', 'c', 'd') choice4) epdp =
  {|enc = epdp_choice4_enc epdp1 epdp2 epdp3 epdp4;
    dec = epdp_choice4_dec epdp1 epdp2 epdp3 epdp4|}.

lemma valid_epdp_choice4
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 =>
  valid_epdp (epdp_choice4 epdp1 epdp2 epdp3 epdp4).
proof.
move => valid1 valid2 valid3 valid4.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice4 /epdp_choice4_enc /epdp_choice4_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice4 /epdp_choice4_enc /epdp_choice4_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
case b => y /=.
by case (epdp3.`dec x).
by case (epdp3.`dec x).
move => match_eq_some.
have val_x : epdp3.`dec x = Some y.
  move : match_eq_some.
  by case (epdp3.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp3.`dec x).
case b => y /=.
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
move => match_eq_some.
have val_x : epdp4.`dec x = Some y.
  move : match_eq_some.
  by case (epdp4.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice4.

(* choice5 EPDPs *)

type ('a, 'b, 'c, 'd, 'e) choice5 = [
  | Choice5_1 of 'a
  | Choice5_2 of 'b
  | Choice5_3 of 'c
  | Choice5_4 of 'd
  | Choice5_5 of 'e
].

op nosmt epdp_choice5_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp,
      ch : ('a, 'b, 'c, 'd, 'e) choice5)
       : ('a', 'b', 'c', 'd', 'e') choice5 =
  match ch with
  | Choice5_1 x => Choice5_1 (epdp1.`enc x)
  | Choice5_2 x => Choice5_2 (epdp2.`enc x)
  | Choice5_3 x => Choice5_3 (epdp3.`enc x)
  | Choice5_4 x => Choice5_4 (epdp4.`enc x)
  | Choice5_5 x => Choice5_5 (epdp5.`enc x)
  end.

op nosmt epdp_choice5_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp,
      ch : ('a', 'b', 'c', 'd', 'e') choice5)
       : ('a, 'b, 'c, 'd, 'e) choice5 option =
  match ch with
  | Choice5_1 x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (Choice5_1 y)
      end
  | Choice5_2 x  =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (Choice5_2 y)
      end
  | Choice5_3 x  =>
      match epdp3.`dec x with
      | None   => None
      | Some y => Some (Choice5_3 y)
      end
  | Choice5_4 x  =>
      match epdp4.`dec x with
      | None   => None
      | Some y => Some (Choice5_4 y)
      end
  | Choice5_5 x  =>
      match epdp5.`dec x with
      | None   => None
      | Some y => Some (Choice5_5 y)
      end
  end.

op nosmt epdp_choice5
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp) :
     (('a, 'b, 'c, 'd, 'e) choice5,
      ('a', 'b', 'c', 'd', 'e') choice5) epdp =
  {|enc = epdp_choice5_enc epdp1 epdp2 epdp3 epdp4 epdp5;
    dec = epdp_choice5_dec epdp1 epdp2 epdp3 epdp4 epdp5|}.

lemma valid_epdp_choice5
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 =>
  valid_epdp (epdp_choice5 epdp1 epdp2 epdp3 epdp4 epdp5).
proof.
move => valid1 valid2 valid3 valid4 valid5.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice5 /epdp_choice5_enc /epdp_choice5_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice5 /epdp_choice5_enc /epdp_choice5_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
case b => y /=.
by case (epdp3.`dec x).
by case (epdp3.`dec x).
move => match_eq_some.
have val_x : epdp3.`dec x = Some y.
  move : match_eq_some.
  by case (epdp3.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
case b => y /=.
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
move => match_eq_some.
have val_x : epdp4.`dec x = Some y.
  move : match_eq_some.
  by case (epdp4.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp4.`dec x).
case b => y /=.
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
move => match_eq_some.
have val_x : epdp5.`dec x = Some y.
  move : match_eq_some.
  by case (epdp5.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice5.

(* choice6 EPDPs *)

type ('a, 'b, 'c, 'd, 'e, 'f) choice6 = [
  | Choice6_1 of 'a
  | Choice6_2 of 'b
  | Choice6_3 of 'c
  | Choice6_4 of 'd
  | Choice6_5 of 'e
  | Choice6_6 of 'f
].

op nosmt epdp_choice6_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      ch : ('a, 'b, 'c, 'd, 'e, 'f) choice6)
       : ('a', 'b', 'c', 'd', 'e', 'f') choice6 =
  match ch with
  | Choice6_1 x => Choice6_1 (epdp1.`enc x)
  | Choice6_2 x => Choice6_2 (epdp2.`enc x)
  | Choice6_3 x => Choice6_3 (epdp3.`enc x)
  | Choice6_4 x => Choice6_4 (epdp4.`enc x)
  | Choice6_5 x => Choice6_5 (epdp5.`enc x)
  | Choice6_6 x => Choice6_6 (epdp6.`enc x)
  end.

op nosmt epdp_choice6_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      ch : ('a', 'b', 'c', 'd', 'e', 'f') choice6)
       : ('a, 'b, 'c, 'd, 'e, 'f) choice6 option =
  match ch with
  | Choice6_1 x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (Choice6_1 y)
      end
  | Choice6_2 x  =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (Choice6_2 y)
      end
  | Choice6_3 x  =>
      match epdp3.`dec x with
      | None   => None
      | Some y => Some (Choice6_3 y)
      end
  | Choice6_4 x  =>
      match epdp4.`dec x with
      | None   => None
      | Some y => Some (Choice6_4 y)
      end
  | Choice6_5 x  =>
      match epdp5.`dec x with
      | None   => None
      | Some y => Some (Choice6_5 y)
      end
  | Choice6_6 x  =>
      match epdp6.`dec x with
      | None   => None
      | Some y => Some (Choice6_6 y)
      end
  end.

op nosmt epdp_choice6
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp) :
     (('a, 'b, 'c, 'd, 'e, 'f) choice6,
      ('a', 'b', 'c', 'd', 'e', 'f') choice6) epdp =
  {|enc = epdp_choice6_enc epdp1 epdp2 epdp3 epdp4 epdp5 epdp6;
    dec = epdp_choice6_dec epdp1 epdp2 epdp3 epdp4 epdp5 epdp6|}.

lemma valid_epdp_choice6
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp (epdp_choice6 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice6 /epdp_choice6_enc /epdp_choice6_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice6 /epdp_choice6_enc /epdp_choice6_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
case b => y /=.
by case (epdp3.`dec x).
by case (epdp3.`dec x).
move => match_eq_some.
have val_x : epdp3.`dec x = Some y.
  move : match_eq_some.
  by case (epdp3.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
case b => y /=.
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
move => match_eq_some.
have val_x : epdp4.`dec x = Some y.
  move : match_eq_some.
  by case (epdp4.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
case b => y /=.
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
move => match_eq_some.
have val_x : epdp5.`dec x = Some y.
  move : match_eq_some.
  by case (epdp5.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp5.`dec x).
case b => y /=.
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
move => match_eq_some.
have val_x : epdp6.`dec x = Some y.
  move : match_eq_some.
  by case (epdp6.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice6.

(* choice7 EPDPs *)

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) choice7 = [
  | Choice7_1 of 'a
  | Choice7_2 of 'b
  | Choice7_3 of 'c
  | Choice7_4 of 'd
  | Choice7_5 of 'e
  | Choice7_6 of 'f
  | Choice7_7 of 'g
].

op nosmt epdp_choice7_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp,
      ch : ('a, 'b, 'c, 'd, 'e, 'f, 'g) choice7)
       : ('a', 'b', 'c', 'd', 'e', 'f', 'g') choice7 =
  match ch with
  | Choice7_1 x => Choice7_1 (epdp1.`enc x)
  | Choice7_2 x => Choice7_2 (epdp2.`enc x)
  | Choice7_3 x => Choice7_3 (epdp3.`enc x)
  | Choice7_4 x => Choice7_4 (epdp4.`enc x)
  | Choice7_5 x => Choice7_5 (epdp5.`enc x)
  | Choice7_6 x => Choice7_6 (epdp6.`enc x)
  | Choice7_7 x => Choice7_7 (epdp7.`enc x)
  end.

op nosmt epdp_choice7_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp,
      ch : ('a', 'b', 'c', 'd', 'e', 'f', 'g') choice7)
       : ('a, 'b, 'c, 'd, 'e, 'f, 'g) choice7 option =
  match ch with
  | Choice7_1 x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (Choice7_1 y)
      end
  | Choice7_2 x  =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (Choice7_2 y)
      end
  | Choice7_3 x  =>
      match epdp3.`dec x with
      | None   => None
      | Some y => Some (Choice7_3 y)
      end
  | Choice7_4 x  =>
      match epdp4.`dec x with
      | None   => None
      | Some y => Some (Choice7_4 y)
      end
  | Choice7_5 x  =>
      match epdp5.`dec x with
      | None   => None
      | Some y => Some (Choice7_5 y)
      end
  | Choice7_6 x  =>
      match epdp6.`dec x with
      | None   => None
      | Some y => Some (Choice7_6 y)
      end
  | Choice7_7 x  =>
      match epdp7.`dec x with
      | None   => None
      | Some y => Some (Choice7_7 y)
      end
  end.

op nosmt epdp_choice7
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp) :
     (('a, 'b, 'c, 'd, 'e, 'f, 'g) choice7,
      ('a', 'b', 'c', 'd', 'e', 'f', 'g') choice7) epdp =
  {|enc = epdp_choice7_enc epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7;
    dec = epdp_choice7_dec epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7|}.

lemma valid_epdp_choice7
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
       epdp7 : ('g, 'g') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 =>
  valid_epdp (epdp_choice7 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice7 /epdp_choice7_enc /epdp_choice7_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice7 /epdp_choice7_enc /epdp_choice7_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
case b => y /=.
by case (epdp3.`dec x).
by case (epdp3.`dec x).
move => match_eq_some.
have val_x : epdp3.`dec x = Some y.
  move : match_eq_some.
  by case (epdp3.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
case b => y /=.
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
move => match_eq_some.
have val_x : epdp4.`dec x = Some y.
  move : match_eq_some.
  by case (epdp4.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
case b => y /=.
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
move => match_eq_some.
have val_x : epdp5.`dec x = Some y.
  move : match_eq_some.
  by case (epdp5.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
case b => y /=.
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
move => match_eq_some.
have val_x : epdp6.`dec x = Some y.
  move : match_eq_some.
  by case (epdp6.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp6.`dec x).
case b => y /=.
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
move => match_eq_some.
have val_x : epdp7.`dec x = Some y.
  move : match_eq_some.
  by case (epdp7.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice7.

(* choice8 EPDPs *)

type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) choice8 = [
  | Choice8_1 of 'a
  | Choice8_2 of 'b
  | Choice8_3 of 'c
  | Choice8_4 of 'd
  | Choice8_5 of 'e
  | Choice8_6 of 'f
  | Choice8_7 of 'g
  | Choice8_8 of 'h
].

op nosmt epdp_choice8_enc
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp,
      ch : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) choice8)
       : ('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h') choice8 =
  match ch with
  | Choice8_1 x => Choice8_1 (epdp1.`enc x)
  | Choice8_2 x => Choice8_2 (epdp2.`enc x)
  | Choice8_3 x => Choice8_3 (epdp3.`enc x)
  | Choice8_4 x => Choice8_4 (epdp4.`enc x)
  | Choice8_5 x => Choice8_5 (epdp5.`enc x)
  | Choice8_6 x => Choice8_6 (epdp6.`enc x)
  | Choice8_7 x => Choice8_7 (epdp7.`enc x)
  | Choice8_8 x => Choice8_8 (epdp8.`enc x)
  end.

op nosmt epdp_choice8_dec
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp,
      ch : ('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h') choice8)
       : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) choice8 option =
  match ch with
  | Choice8_1 x  =>
      match epdp1.`dec x with
      | None   => None
      | Some y => Some (Choice8_1 y)
      end
  | Choice8_2 x  =>
      match epdp2.`dec x with
      | None   => None
      | Some y => Some (Choice8_2 y)
      end
  | Choice8_3 x  =>
      match epdp3.`dec x with
      | None   => None
      | Some y => Some (Choice8_3 y)
      end
  | Choice8_4 x  =>
      match epdp4.`dec x with
      | None   => None
      | Some y => Some (Choice8_4 y)
      end
  | Choice8_5 x  =>
      match epdp5.`dec x with
      | None   => None
      | Some y => Some (Choice8_5 y)
      end
  | Choice8_6 x  =>
      match epdp6.`dec x with
      | None   => None
      | Some y => Some (Choice8_6 y)
      end
  | Choice8_7 x  =>
      match epdp7.`dec x with
      | None   => None
      | Some y => Some (Choice8_7 y)
      end
  | Choice8_8 x  =>
      match epdp8.`dec x with
      | None   => None
      | Some y => Some (Choice8_8 y)
      end
  end.

op nosmt epdp_choice8
     (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
      epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
      epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
      epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp) :
     (('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) choice8,
      ('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h') choice8) epdp =
  {|enc = epdp_choice8_enc epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8;
    dec = epdp_choice8_dec epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8|}.

lemma valid_epdp_choice8
      (epdp1 : ('a, 'a') epdp, epdp2 : ('b, 'b') epdp,
       epdp3 : ('c, 'c') epdp, epdp4 : ('d, 'd') epdp,
       epdp5 : ('e, 'e') epdp, epdp6 : ('f, 'f') epdp,
       epdp7 : ('g, 'g') epdp, epdp8 : ('h, 'h') epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 => valid_epdp epdp8 =>
  valid_epdp (epdp_choice8 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).
proof.
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7 valid8.
rewrite epdp_intro => [x | a b].
rewrite /epdp_choice8 /epdp_choice8_enc /epdp_choice8_dec /=.
case x => y /=; by rewrite epdp_enc_dec.
rewrite /epdp_choice8 /epdp_choice8_enc /epdp_choice8_dec /=.
case a => x /=.
case b => y /=.
move => match_eq_some.
have val_x : epdp1.`dec x = Some y.
  move : match_eq_some.
  by case (epdp1.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
by case (epdp1.`dec x).
case b => y /=.
by case (epdp2.`dec x).
move => match_eq_some.
have val_x : epdp2.`dec x = Some y.
  move : match_eq_some.
  by case (epdp2.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
by case (epdp2.`dec x).
case b => y /=.
by case (epdp3.`dec x).
by case (epdp3.`dec x).
move => match_eq_some.
have val_x : epdp3.`dec x = Some y.
  move : match_eq_some.
  by case (epdp3.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
by case (epdp3.`dec x).
case b => y /=.
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
move => match_eq_some.
have val_x : epdp4.`dec x = Some y.
  move : match_eq_some.
  by case (epdp4.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
by case (epdp4.`dec x).
case b => y /=.
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
move => match_eq_some.
have val_x : epdp5.`dec x = Some y.
  move : match_eq_some.
  by case (epdp5.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
by case (epdp5.`dec x).
case b => y /=.
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
move => match_eq_some.
have val_x : epdp6.`dec x = Some y.
  move : match_eq_some.
  by case (epdp6.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp6.`dec x).
by case (epdp6.`dec x).
case b => y /=.
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
by case (epdp7.`dec x).
move => match_eq_some.
have val_x : epdp7.`dec x = Some y.
  move : match_eq_some.
  by case (epdp7.`dec x).
by rewrite (epdp_dec_enc _ _ x).
by case (epdp7.`dec x).
case b => y /=.
by case (epdp8.`dec x).
by case (epdp8.`dec x).
by case (epdp8.`dec x).
by case (epdp8.`dec x).
by case (epdp8.`dec x).
by case (epdp8.`dec x).
by case (epdp8.`dec x).
move => match_eq_some.
have val_x : epdp8.`dec x = Some y.
  move : match_eq_some.
  by case (epdp8.`dec x).
by rewrite (epdp_dec_enc _ _ x).
qed.

hint rewrite epdp_sub : valid_epdp_choice8.

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
