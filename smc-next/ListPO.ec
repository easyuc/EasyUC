(* ListPO.ec *)

(* Prefix Ordering on Lists *)

prover [""].  (* no provers *)

(* We define a partial ordering between lists xs and ys: xs is
   less-than-or-equal-to ys iff xs is a prefix of ys, i.e.,
   concatenating (possibly nothing) to the end of xs will form ys

   We actually implement this as an operator producing one of four
   results, and only later define the expected binary relations *)

require import AllCore List ListAux.

(* comparison results *)

type resu = [
  | Eq   (* first equals second *)
  | LT   (* first less than second *)
  | GT   (* first greater than second *)
  | Inc  (* first and second imcomparable *)
].

(* comparison operator *)

op lpo (xs ys : 'a list) : resu =
  with xs = []      =>
    ((ys = []) ? Eq : LT)
  with xs = u :: us =>
    ((ys = []) ?
     GT :
     let (v, vs) = (head u ys, behead ys)
     in ((u = v) ? lpo us vs : Inc)).

(* inductive predicates for relationships *)

inductive le_spec (xs ys : 'a list) =
  | LES (us : 'a list) of
      (xs ++ us = ys).

inductive lt_spec (xs ys : 'a list) =
  | LTS (us : 'a list) of
        (us <> [])
      & (xs ++ us = ys).

inductive inc_spec (xs ys : 'a list) =
  | IncS (x y : 'a, us vs ws : 'a list) of
        (x <> y)
      & (xs = us ++ [x] ++ vs)
      & (ys = us ++ [y] ++ ws).

lemma lpo_nil :
  lpo <:'a>[] [] = Eq.
proof. done. qed.

lemma lpo_nil_non_nil (y : 'a, ys : 'a list) :
  lpo [] (y :: ys) = LT.
proof. done. qed.

lemma lpo_non_nil_nil (x : 'a, xs : 'a list) :
  lpo (x :: xs) [] = GT.
proof. done. qed.

lemma lpo_non_nil_eq (x y : 'a, xs ys : 'a list) :
  x = y => lpo (x :: xs) (y :: ys) = lpo xs ys.
proof. done. qed.

lemma lpo_non_nil_ne (x y : 'a, xs ys : 'a list) :
  x <> y => lpo (x :: xs) (y :: ys) = Inc.
proof.
move => ne_xy; by rewrite /= ne_xy.
qed.

lemma lpo_eqP (xs ys : 'a list) :
  lpo xs ys = Eq <=> xs = ys.
proof.
split.
move : ys; elim xs.
case; done.
move => x xs IH [] // y ys.
case (x = y) => [-> /= | /= -> //].
apply IH.
move => ->; elim ys; done.
qed.

lemma lpo_ltP (xs ys : 'a list) :
  lpo xs ys = LT <=> lt_spec xs ys.
proof.
split.
move : ys; elim xs.
case => // x xs _.
apply (LTS [] (x :: xs) (x :: xs)).
move => x xs IH [] // y ys.
case (x = y) => [-> /= lt | /= -> //].
have [] us us_ne_nil <- := (IH ys lt).
by apply (LTS (y :: xs) (y :: (xs ++ us)) us).
case => us us_ne_nil <-.
elim xs => //=.
by rewrite us_ne_nil.
qed.

lemma lpo_gtP (xs ys : 'a list) :
  lpo xs ys = GT <=> lt_spec ys xs.
proof.
split.
move : xs; elim ys.
case => // y ys _.
apply (LTS [] (y :: ys) (y :: ys)).
move => y ys IH [] // x xs.
case (x = y) => [-> /= gt | /= -> //].
have [] us us_ne_nil <- := (IH xs gt).
by apply (LTS (y :: ys) (y :: (ys ++ us)) us).
case => us us_ne_nil <- //.
move : us us_ne_nil.
case => // u us _.
by elim ys.
qed.

lemma lpo_sym_lt_gt (xs ys : 'a list) :
  lpo xs ys = LT <=> lpo ys xs = GT.
proof.
split.
move => /lpo_ltP lts.
by rewrite lpo_gtP.
move => /lpo_gtP lts.
by rewrite lpo_ltP.
qed.

lemma lpo_lt_trans (ys xs zs : 'a list) :
  lpo xs ys = LT => lpo ys zs = LT =>
  lpo xs zs = LT.
proof.
move => /lpo_ltP [] us us_ne_nil <-.
move => /lpo_ltP [] vs vs_ne_nil <-.
rewrite lpo_ltP -catA
        (LTS xs (xs ++ (us ++ vs)) (us ++ vs)) //.
move : us vs us_ne_nil vs_ne_nil; by case.
qed.

lemma lpo_gt_trans (ys xs zs : 'a list) :
  lpo xs ys = GT => lpo ys zs = GT =>
  lpo xs zs = GT.
proof.
move => /lpo_gtP [] us us_ne_nil <-.
move => /lpo_gtP [] vs vs_ne_nil <-.
rewrite lpo_gtP -catA
        (LTS zs (zs ++ (vs ++ us)) (vs ++ us)) //.
move : vs us us_ne_nil vs_ne_nil; by case.
qed.

lemma lpo_incP (xs ys : 'a list) :
  lpo xs ys = Inc <=> inc_spec xs ys.
proof.
split.
move : ys; elim xs.
case; done.
move => x xs IH [] // y ys.
case (x = y) => [-> /= inc | ne_xy /=].
have [] x0 y0 us vs ws ne_x0_y0 -> -> := (IH ys inc).
by rewrite -!catA -!cat_cons !catA
           (IncS
            ((y :: us) ++ [x0] ++ vs) ((y :: us) ++ [y0] ++ ws)
            x0 y0 (y :: us) vs ws)
           // ne_x0_y0.
by rewrite ne_xy /=
           (IncS (x :: xs) (y :: ys) x y [] xs ys).
case => x y us vs ws ne_xy -> ->.
elim us => //=; by rewrite ne_xy.
qed.

lemma lpo_inc_sym (xs ys : 'a list) :
  lpo xs ys = Inc <=> lpo ys xs = Inc.
proof.
split.
move => /lpo_incP [] x y us vs ws ne_xy -> ->.
by rewrite lpo_incP
           (IncS (us ++ [y] ++ ws) (us ++ [x] ++ vs)
            y x us ws vs)
           // eq_sym.
move => /lpo_incP [] x y us vs ws ne_xy -> ->.
by rewrite lpo_incP
           (IncS (us ++ [y] ++ ws) (us ++ [x] ++ vs)
            y x us ws vs)
           // eq_sym.
qed.

lemma lpo_inc_ext1 (xs ys zs : 'a list) :
  lpo xs ys = Inc => lpo (xs ++ zs) ys = Inc.
proof.
move => /lpo_incP [] x0 y0 us vs ws x0_ne_y0 -> ->.
by rewrite -catA lpo_incP
           (IncS
            (us ++ [x0] ++ (vs ++ zs)) (us ++ [y0] ++ ws)
            x0 y0 us (vs ++ zs) ws).
qed.

lemma lpo_inc_ext2 (xs ys zs : 'a list) :
  lpo xs ys = Inc => lpo xs (ys ++ zs) = Inc.
proof.
move => /lpo_incP [] x0 y0 us vs ws x0_ne_y0 -> ->.
by rewrite -(catA (us ++ [y0])) lpo_incP
           (IncS
            (us ++ [x0] ++ vs) (us ++ [y0] ++ (ws ++ zs))
            x0 y0 us vs (ws ++ zs)).
qed.

lemma lpo_inc_ext (xs ys zs ws : 'a list) :
  lpo xs ys = Inc => lpo (xs ++ zs) (ys ++ ws) = Inc.
proof.
move => /lpo_incP [] x y us vs ws0 x_ne_0 -> ->.
by rewrite -catA -(catA (us ++ [y])) lpo_incP
           (IncS
            (us ++ [x] ++ (vs ++ zs)) (us ++ [y] ++ (ws0 ++ ws))
            x y us (vs ++ zs) (ws0 ++ ws)).
qed.

(* abbreviations *)

op (<) (xs ys : 'a list) : bool = lpo xs ys = LT.

op (<=) (xs ys : 'a list) : bool =
  let r = lpo xs ys in r = LT \/ r = Eq.

op inc (xs ys : 'a list) : bool = lpo xs ys = Inc.

lemma leP (xs ys : 'a list) :
  xs <= ys <=> le_spec xs ys.
proof.
split.
move => @/(<=) /= [].
move => /lpo_ltP [] us nonnil_us xs_us_eq_ys.
by rewrite (LES xs ys us).
move => /lpo_eqP ->.
by rewrite (LES ys ys []) cats0.
rewrite /(<=) /=.
case => us xs_us_eq_ys.
case (us = []) => [nil_us | nonnil_us].
right; by rewrite lpo_eqP -xs_us_eq_ys nil_us cats0.
left; by rewrite lpo_ltP (LTS xs ys us).
qed.

lemma le_drop (xs ys : 'a list) :
  xs <= ys => xs ++ drop (size xs) ys = ys.
proof.
move => /leP [] us <-.
congr; by rewrite drop_size_cat.
qed.

lemma lt_trans (ys xs zs : 'a list) :
  xs < ys => ys < zs => xs < zs.
proof.
move => @/(<) />; apply lpo_lt_trans.
qed.

lemma le_refl (xs : 'a list) : xs <= xs.
proof.
rewrite /(<=) /=.
right; by rewrite lpo_eqP.
qed.

lemma le_trans (ys xs zs : 'a list) :
  xs <= ys => ys <= zs => xs <= zs.
proof.
move => @/(<=) />.
case => [lt_xs_ys | /lpo_eqP ->].
case => [lt_ys_zs | /lpo_eqP <-].
left; by apply (lpo_lt_trans ys).
by left.
case => [lt_ys_zs | /lpo_eqP <-].
by left.
right; by rewrite lpo_eqP.
qed.

lemma le_anti (xs ys : 'a list) :
  xs <= ys => ys <= xs => xs = ys.
proof.
move => @/(<=) /> [lt_xs_ys | /lpo_eqP ->].
move => [lt_ys_xs | /lpo_eqP -> //].
rewrite lpo_sym_lt_gt in lt_ys_xs.
have // : LT = GT by rewrite -lt_xs_ys lt_ys_xs.
by move => [lt_ys_ys | /lpo_eqP ->].
qed.

lemma ltW (xs ys : 'a list) :
  xs < ys => xs <= ys.
proof. move => @/(<=) @/(<) />. qed.

lemma le_lt_trans (ys xs zs : 'a list) :
  xs <= ys => ys < zs => xs < zs.
proof.
move => @/(<=) @/(<) />.
case => [lt_xs_ys lt_ys_zs | /lpo_eqP -> //].
by rewrite (lpo_lt_trans ys).
qed.

lemma lt_le_trans (ys xs zs : 'a list) :
  xs < ys => ys <= zs => xs < zs.
proof.
move => @/(<=) @/(<) />.
move => lt_xs_ys.
case => [lt_ys_zs | /lpo_eqP <- //].
by rewrite (lpo_lt_trans ys).
qed.

lemma not_leP (xs ys : 'a list) :
  !(xs <= ys) <=> ys < xs \/ inc xs ys.
proof.
split.
rewrite /(<=) /(<) /= /inc (lpo_sym_lt_gt ys xs) negb_or.
by case (lpo xs ys).
rewrite /(<=) /(<) /lpo_inc /= (lpo_sym_lt_gt ys xs)
        negb_or.
by case => ->.
qed.

lemma inc_sym (xs ys : 'a list) :
  inc xs ys <=> inc ys xs.
proof.
by rewrite /inc lpo_inc_sym.
qed.

lemma inc_nle_l (xs ys : 'a list) :
  inc xs ys => !(xs <= ys).
proof.
rewrite /inc /(<=) /=.
by move => ->.
qed.

lemma inc_nle_r (xs ys : 'a list) :
  inc xs ys => !(ys <= xs).
proof.
rewrite inc_sym.
apply inc_nle_l.
qed.

lemma incP (xs ys : 'a list) :
  inc xs ys <=> !(xs <= ys) /\ !(ys <= xs).
proof.
split.
move => inc_xs_ys.
split; [by rewrite inc_nle_l | by rewrite inc_nle_r].
move => [#]; rewrite not_leP.
move => [] //.
rewrite /(<) /(<=) /inc /= negb_or.
by move => ->.
qed.

lemma inc_ext1 (xs ys zs : 'a list) :
  inc xs ys => inc (xs ++ zs) ys.
proof.
rewrite /inc; apply lpo_inc_ext1.
qed.

lemma inc_ext2 (xs ys zs : 'a list) :
  inc xs ys => inc xs (ys ++ zs).
proof.
rewrite /inc; apply lpo_inc_ext2.
qed.

lemma inc_le1_not_rl (xs ys zs : 'a list) :
  inc xs ys => xs <= zs => !(ys <= zs).
proof.
move => lpo_inc_xs_ys /@leP [us <-].
by rewrite not_leP inc_sym inc_ext1.
qed.

lemma inc_le1_not_lr (xs ys zs : 'a list) :
  inc xs ys => xs <= zs => !(zs <= ys).
proof.
move => lpo_inc_xs_ys /@leP [us <-].
by rewrite not_leP inc_ext1.
qed.

lemma inc_le2_not_lr (xs ys zs : 'a list) :
  inc xs ys => ys <= zs => !(xs <= zs).
proof.
move => /@inc_sym; apply inc_le1_not_rl.
qed.

lemma inc_le2_not_rl (xs ys zs : 'a list) :
  inc xs ys => ys <= zs => !(zs <= xs).
proof.
move => /@inc_sym; apply inc_le1_not_lr.
qed.

lemma lt_ext_nonnil_r (xs ys : 'a list) :
  ys <> [] => xs < xs ++ ys.
proof.
move => nonnil_ys.
by rewrite /(<) lpo_ltP (LTS xs (xs ++ ys) ys).
qed.

lemma le_ext_r (xs ys : 'a list) :
  xs <= xs ++ ys.
proof.
by rewrite leP (LES xs (xs ++ ys) ys).
qed.

lemma le_ext_comm (xs ys zs : 'a list) :
  xs ++ ys <= xs ++ zs <=> ys <= zs.
proof.
rewrite 2!leP; split.
case => us eq.
by rewrite (LES ys zs us) (catsI xs (ys ++ us) zs) 1:catA.
case => us eq.
by rewrite (LES (xs ++ ys) (xs ++ zs) us) -eq catA.
qed.

lemma sing_not_le (x y : 'a) :
  x <> y => ! [x] <= [y].
proof.
move => ne_xy; rewrite leP.
case (! le_spec [x] [y]) => // contrad.
rewrite /= in contrad.
case contrad => us eq.
have x_eq : nth x ([x] ++ us) 0 = x.
  by rewrite cat1s /=.
have y_eq : nth x [y] 0 = y by trivial.
have // : x = y by rewrite -x_eq -y_eq; congr.
qed.

lemma not_le_other_branch (xs zs : 'a list, x y : 'a) :
  x <> y => xs ++ [x] <= zs => ! (xs ++ [y] <= zs).
proof.
move => ne_xy /leP le_xs_x_zs.
case (xs ++ [y] <= zs) => [/leP [us <<-] | //].
case le_xs_x_zs => vs eq.
have eq2 : [x] ++ vs = [y] ++ us
  by rewrite (catsI xs ([x] ++ vs) ([y] ++ us)) 1:!catA.
have // : x = y.
  have -> : y = head y ([y] ++ vs) by trivial.
  have -> : x = head x ([x] ++ vs) by trivial.
  by rewrite eq2.
qed.

lemma not_le_ext_nonnil_l (xs ys : 'a list) :
  ys <> [] => ! xs ++ ys <= xs.
proof.
move => nonnil_ys.
case (xs ++ ys <= xs) => [/leP [us eq] | //].
rewrite -catA in eq.
have // := (ne_cat_nonnil_r xs (ys ++ us) _).
  by apply nonnil_cat_nonnil_l.
qed.

lemma ge_nonnil_ext_imp_ne (xs ys zs : 'a list) :
  ys <> [] => xs ++ ys <= zs => zs <> xs.
proof.
move => nonnil_ys /leP [us <-].
by rewrite -catA ne_cat_nonnil_r // nonnil_cat_nonnil_l.
qed.

lemma not_le_ext (xs ys zs : 'a list) :
  ! xs <= ys => ! xs ++ zs <= ys.
proof.
move => not_le_xs_ys.
case (xs ++ zs <= ys) => [not_le_xs_conc_zs_ys | //].
have // : xs <= ys by rewrite (le_trans (xs ++ zs)) 1:le_ext_r.
qed.
