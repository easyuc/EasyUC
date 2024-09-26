(* Univ.ec *)

(* Universe of Values Plus EPDPs on Universe *)

prover [""].  (* no use of SMT provers *)

require import AllCore List StdOrder IntDiv BitEncoding UCEncoding WF.
import IntOrder BS2Int.

(* search for "universe" for the definition of the type univ
   followed by the EPDPs on univ *)

(* auxiliary definitions and lemmas *)

(* integer logarithms for use below (EasyCrypt now provides these via
   log on reals, but we prefer to work directly with ints, using a
   strong induction that could be turned into recursive definition) *)

lemma exists_int_log (b n : int) :
  2 <= b => 1 <= n =>
  exists (k : int), 0 <= k /\ b ^ k <= n < b ^ (k + 1).
proof.
move => ge2_b ge1_n.
have gt1_b : 1 < b by rewrite ltzE.
have gt0_b : 0 < b by rewrite (ltr_trans 1).
have ge0_b : 0 <= b by rewrite ltrW.
have H :
  forall n,
  0 <= n => 1 <= n =>
  exists (k : int), 0 <= k /\ b ^ k <= n < b ^ (k + 1).
  apply sintind => i ge0_i IH /= ge1_i.
  case (i < b) => [lt_i_b | ge_b_i].
  exists 0; by rewrite /= expr0 ge1_i /= expr1.
  rewrite -lerNgt in ge_b_i.
  have [ge1_i_div_b i_div_b_lt_i] : 1 <= i %/ b < i.
    split => [| _].
    by rewrite lez_divRL 1:gt0_b.
    by rewrite ltz_divLR 1:gt0_b -divr1 mulzA 1:ltr_pmul2l ltzE.
  have /= [k [#] ge0_k b_exp_k_le_i_div_b i_div_b_lt_b_tim_b_exp_k]
       := IH (i %/ b) _ _.
    split; [by rewrite (lez_trans 1) | trivial].
    trivial.
  rewrite exprS // in i_div_b_lt_b_tim_b_exp_k.
  exists (k + 1).
  split; first by rewrite ler_paddl.
  rewrite exprS // mulzC exprS 1:ler_paddr // exprS //.
  split => [| _].
  rewrite (lez_trans ((i %/ b) * b)).
  by rewrite ler_wpmul2r 1:(lez_trans 2).
  by rewrite leq_trunc_div 1:(lez_trans 1).
  rewrite ltz_divLR // in i_div_b_lt_b_tim_b_exp_k.
  by rewrite mulzC.
by rewrite H (lez_trans 1).
qed.

lemma int_log_uniq (b n k1 k2 : int) :
  2 <= b =>
  0 <= k1 => b ^ k1 <= n => n < b ^ (k1 + 1) =>
  0 <= k2 => b ^ k2 <= n => n < b ^ (k2 + 1) =>
  k1 = k2.
proof.
move => ge2_b ge0_k1 b2k1_le_n n_lt_b2k1p1 ge0_k2 b2k2_le_n n_lt_b2k2p1.
have ge1_b : 1 <= b.
  by rewrite (lez_trans 2).
case (k1 = k2) => [// | /ltr_total [lt_k1_k2 | lt_k2_k1]].
rewrite ltzE in lt_k1_k2.
have b2k1p1_le_b2k2 : b ^ (k1 + 1) <= b ^ k2.
  by rewrite ler_weexpn2l // lt_k1_k2 /= addr_ge0.
have // : n < n.
  by rewrite (ltr_le_trans (b ^ (k1 + 1))) // (lez_trans (b ^ k2)).
rewrite ltzE in lt_k2_k1.
have b2k2p1_le_b2k1 : b ^ (k2 + 1) <= b ^ k1.
  by rewrite ler_weexpn2l // lt_k2_k1 /= addr_ge0.
have // : n < n.
  by rewrite (ltr_le_trans (b ^ (k2 + 1))) // (lez_trans (b ^ k1)).
qed.

op int_log (b n : int) : int = (* integer logarithm *)
  choiceb
  (fun (k : int) => 0 <= k /\ b ^ k <= n < b ^ (k + 1))
  0.

lemma int_logP (b n : int) :
  2 <= b => 1 <= n =>
  0 <= int_log b n /\ b ^ (int_log b n) <= n < b ^ (int_log b n + 1).
proof.
move => ge2_b ge1_n.
have // := choicebP (fun k => 0 <= k /\ b ^ k <= n < b ^ (k + 1)) 0 _.
  by rewrite /= exists_int_log.
qed.

lemma int_logPuniq (b n l : int) :
  2 <= b =>
  0 <= l => b ^ l <= n < b ^ (l + 1) =>
  l = int_log b n.
proof.
move => ge2_b ge0_n [b2l_le_n n_lt_b2lp1].
have ge1_n : 1 <= n.
  by rewrite (lez_trans (b ^ l)) // exprn_ege1 // (lez_trans 2).
have := int_logP b n _ _ => // [#] ge0_il b2il_le_n n_lt_b2ilp1.
by apply (int_log_uniq b n).
qed.

lemma ge0_int_log (b n : int) :
  2 <= b => 1 <= n => 0 <= int_log b n.
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

(* int2bs (see BitEncoding), for 1 <= n, with minimum number of
   bits: *)

op int2bs_min (n : int) : bool list = int2bs (int_log 2 n + 1) n.

lemma int2bs_min_nonempty (n : int) :
  1 <= n => int2bs_min n <> [].
proof.
move => ge1_n.
rewrite /int2bs_min.
have [#] := int_logP 2 n _ _ => //.
pose N := int_log 2 n.
move => ge0_N two2N_le_n n_lt_two2Np1.
by rewrite -size_eq0 size_int2bs // ler_maxr 1:ler_paddr //
           gtr_eqF 1:ltzS.
qed.

lemma div_self (n : int) :
  n <> 0 => n %/ n = 1.
proof.
move => ne0_n.
by rewrite divzz /b2i ne0_n.
qed.

(* most significant (which is last) element of int2bs_min n
   is true: *)

lemma int2bs_min_last (n : int) :
  1 <= n => last false (int2bs_min n).
proof.
move => ge1_n.
rewrite /int2bs_min.
have [#] := int_logP 2 n _ _ => //.
pose N := int_log 2 n.
move => ge0_N two2N_le_n n_lt_two2Np1.
have sizeNp1_eq : size (int2bs (N + 1) n) = N + 1.
  by rewrite size_int2bs ler_maxr 1:ler_paddr.
have sizeN_eq: size (int2bs N n) = N.
  by rewrite size_int2bs ler_maxr /N 1:ge0_N.
rewrite -nth_last sizeNp1_eq /= 1:int2bsS // nth_rcons sizeN_eq /=.
have -> // : n %/ 2 ^ N = 1.
have ge1_ndivtwo2N : 1 <= n %/ 2 ^ N.
  have -> : 1 = 2 ^ N %/ 2 ^ N.
    by rewrite div_self // gtr_eqF 1:expr_gt0.
  by rewrite leq_div2r // expr_ge0.
have ndivtwo2N_le_1 : n %/ 2 ^ N <= 1.
  rewrite -ltzS /=.
  rewrite exprS // in n_lt_two2Np1.
  by rewrite ltz_divLR 1:expr_gt0.
by rewrite eqr_le.
qed.

lemma last_false_nonempty (bs : bool list) :
  last false bs => bs <> [].
proof.
by case bs.
qed.

lemma gt0_bs2int (bs : bool list) :
  last false bs => 0 < bs2int bs.
proof.
case bs => [| z zs /= last_z_zs].
by rewrite bs2int_nil.
by rewrite lastI bs2int_rcons last_z_zs /b2i /= ltr_paddl
           1:bs2int_ge0 expr_gt0.
qed.

lemma size_int_log2 (bs : bool list) :
  last false bs =>
  size bs = int_log 2 (bs2int bs) + 1.
proof.
case bs => [// | z zs /= last_z_zs].
rewrite addzC.
congr.
rewrite lastI bs2int_rcons last_z_zs /b2i /=
        size_belast.
have : 0 <= bs2int (belast z zs) < 2 ^ (size zs).
  split => [| _].
  rewrite bs2int_ge0.
  have -> : size zs = size (belast z zs).
    by rewrite size_belast.
  rewrite bs2int_le2Xs.
pose n := bs2int (belast z zs).
move => [ge0_n n_lt_two2size_zs].
apply int_logPuniq => //.
split => [| _].
by rewrite ler_addr.
by rewrite exprS 1:size_ge0 mulzC -intmulz mulr2z ltr_le_add.
qed.

lemma bs2intK_min (bs : bool list) :
  last false bs => int2bs_min (bs2int bs) = bs.
proof.
move => last_false_bs.
rewrite /int2bs_min.
by rewrite -size_int_log2 // bs2intK.
qed.

(* alternation and de-alternation *)

op alt (y : 'a, xs : 'a list) : 'a list =
  with xs = []      => []
  with xs = z :: zs => y :: z :: alt y zs.

op de_alt_aux (y : 'a, b : bool, ws xs : 'a list)
     : ('a list * 'a list) option =
  with xs = []      =>
    if b then Some (ws, []) else None
  with xs = x :: xs =>
    if b
    then if x = y
         then de_alt_aux y false ws xs
         else Some (ws, x :: xs)
    else de_alt_aux y true (rcons ws x) xs.

op de_alt (y : 'a, xs : 'a list) : ('a list * 'a list) option =
  de_alt_aux y true [] xs.

lemma alt_size (y : 'a, xs : 'a list) :
  size (alt y xs) = 2 * size xs.
proof.
elim xs => [// | z zs IH /=].
by rewrite IH mulrDr.
qed.

lemma alt_de_alt_aux (y : 'a, b : bool, xs zs : 'a list) :
  head y zs <> y =>
  (forall (ws : 'a list),
   de_alt_aux y true ws (alt y xs ++ zs) = Some (ws ++ xs, zs)).
proof.
case zs => [// | z zs]; rewrite /= => head_ne_y.
elim xs => [ws /= | x xs IH ws /=].
by rewrite head_ne_y /= cats0.
rewrite IH.
congr; by rewrite cat_rcons.
qed.

lemma alt_de_alt (y : 'a, xs zs : 'a list) :
  head y zs <> y =>
  de_alt y (alt y xs ++ zs) = Some (xs, zs).
proof.
move => head_ne_y.
by apply (alt_de_alt_aux y true).
qed.

lemma de_alt_aux_alt (y : 'a, us : 'a list) :
  (forall (xs, ws, zs : 'a list),
   de_alt_aux y true ws us = Some (xs, zs) =>
   (zs = [] \/ head y zs <> y) /\
   exists (cs ds : 'a list),
   us = cs ++ zs /\ xs = ws ++ ds /\ alt y ds = cs) /\
  (forall (xs, ws, zs : 'a list),
   de_alt_aux y false ws us = Some (xs, zs) =>
   (zs = [] \/ head y zs <> y) /\
   exists (b : 'a, cs ds : 'a list),
   us = b :: cs ++ zs /\ xs = ws ++ [b] ++ ds /\
   alt y ds = cs).
proof.
elim us => [| u us [IH1 IH2]].
split => [xs ws zs /= [<- <-] | xs ws zs //].
exists [] []; by rewrite /= cats0.
split => [xs ws zs /= | xs ws zs /= /IH1 [-> [cs ds [#] -> -> <-]] /=].
case (u = y) =>
  [-> /IH2 [-> /= [b cs ds] [#] -> -> <-] | ne_u_y /= [-> <-] /=].
exists (alt y ([b] ++ ds)) ([b] ++ ds).
by rewrite /= -!catA cat1s.
rewrite ne_u_y /=.
exists (alt y []) [].
by rewrite /= cats0.
exists u (alt y ds) ds.
by rewrite /= cat_rcons -cat1s catA.
qed.

lemma de_alt_alt (y : 'a, us xs zs : 'a list) :
  de_alt y us = Some (xs, zs) =>
  (zs = [] \/ head y zs <> y) /\ us = alt y xs ++ zs.
proof.
rewrite /de_alt.
have [H _] := de_alt_aux_alt y us.
move => /H [-> [cs ds [#] -> -> <-]] //.
qed.

(* universe *)

type univ = bool list.  (* universe values are lists of bits *)

(* unit encoding: *)

op [opaque smt_opaque] enc_unit (x : unit) : univ = [].

op [opaque smt_opaque] dec_unit (u : univ) : unit option =
  if u = [] then Some () else None.

op [opaque smt_opaque] epdp_unit_univ : (unit, univ) epdp =
  {|enc = enc_unit; dec = dec_unit|}.

lemma valid_epdp_unit_univ : valid_epdp epdp_unit_univ.
proof.
apply epdp_intro => [x | u x].
by rewrite /epdp_unit_univ /= /enc_unit /dec_unit.
rewrite /epdp_unit_univ /= /enc_unit /dec_unit.
by case u.
qed.

hint simplify valid_epdp_unit_univ.
hint rewrite epdp : valid_epdp_unit_univ.

(* bool encoding: *)

op [opaque smt_opaque] enc_bool (b : bool) : univ = [b].

op [opaque smt_opaque] dec_bool (u : univ) : bool option =
  if size u = 1 then Some (head true u) else None.

op [opaque smt_opaque] epdp_bool_univ : (bool, univ) epdp =
  {|enc = enc_bool; dec = dec_bool|}.

lemma valid_epdp_bool_univ : valid_epdp epdp_bool_univ.
proof.
apply epdp_intro => [x | u x].
by rewrite /epdp_bool_univ /= /enc_bool /dec_bool.
rewrite /epdp_bool_univ /= /enc_bool /dec_bool.
case u => [// | y ys /=].
case (1 + size ys = 1) => [size_eq /= -> /=| //].
have /= /size_eq0 -> // : (1 + size ys) - 1 = 1 - 1.
  by rewrite size_eq.
qed.

hint simplify valid_epdp_bool_univ.
hint rewrite epdp : valid_epdp_bool_univ.

(* int encoding: *)

op [opaque smt_opaque] enc_int (n : int) : univ =
  if n = 0
  then []
  else if 0 < n
       then true  :: int2bs_min n
       else false :: int2bs_min (-n).

op [opaque smt_opaque] dec_int (u : univ) : int option =
  match u with
  | []      => Some 0
  | b :: bs =>
      if b
      then if bs = [] \/ ! (last false bs)
           then None
           else Some (bs2int bs)
      else if bs = [] \/ ! (last false bs)
           then None
           else Some (-(bs2int bs))
  end.

op [opaque smt_opaque] epdp_int_univ : (int, univ) epdp =
  {|enc = enc_int; dec = dec_int|}.

lemma valid_epdp_int_univ : valid_epdp epdp_int_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_int_univ /= /enc_int /dec_int /=.
case (x = 0) => [-> // | ne0_x].
case (0 < x) => [gt0_x | not_ge0_x].
pose bs := int2bs_min x.
have [#] ge0_il two2il_le_x x_lt_two2ilp1 := int_logP 2 x _ _ => //.
  by rewrite -add0z -ltzE.
have -> /= : bs <> [].
  rewrite int2bs_min_nonempty //.
  rewrite ltzE // in gt0_x.
have -> /= : last false bs.
  rewrite int2bs_min_last.
  rewrite ltzE // in gt0_x.
rewrite int2bsK 1:ler_paddr //.
split => [| //].
by rewrite ltzW.
have gt0_negx : 0 < -x.
  rewrite -lerNgt -oppz_ge0 in not_ge0_x.
  by rewrite ltr_def not_ge0_x /= oppr_eq0.
pose bs := int2bs_min (-x).
have [#] ge0_il two2il_le_negx negx_lt_two2ilp1
     := int_logP 2 (-x) _ _ => //.
  by rewrite -add0z -ltzE.
have -> /= : bs <> [].
  rewrite int2bs_min_nonempty //.
  rewrite ltzE // in gt0_negx.
have -> /= : last false bs.
  rewrite int2bs_min_last.
  rewrite ltzE // in gt0_negx.
rewrite int2bsK 1:ler_paddr //.
split => [| //].
by rewrite ltzW.
rewrite /epdp_int_univ /= /enc_int /dec_int.
case u => [/= <- // | z zs /=].
case z => _.
case (zs = [] \/ ! last false zs) => [// |].
rewrite negb_or => [/= [zs_ne_nil last_is_true_zs]] <-.
have -> /= : bs2int zs <> 0.
  by rewrite gtr_eqF // gt0_bs2int.
case (0 < bs2int zs) => [gt0_bs2int_zs | not_ge0_bs2int_zs].
congr.
by rewrite bs2intK_min.
rewrite gt0_bs2int // in not_ge0_bs2int_zs.
case (zs = [] \/ ! last false zs) => [// |].
rewrite negb_or => [/= [zs_ne_nil last_is_true_zs]] <-.
have -> /= : - bs2int zs <> 0.
  by rewrite eq_sym gtr_eqF // oppr_lt0 gt0_bs2int.
case (0 < - bs2int zs) => [gt0_negbs2int_zs | not_ge0_negbs2int_zs].
rewrite oppz_gt0 in gt0_negbs2int_zs.
have gt0_bs2int_zs := gt0_bs2int zs _ => //.
have // : 0 < 0 by rewrite (ltr_trans (bs2int zs)).
congr.
by rewrite bs2intK_min.
qed.

hint simplify valid_epdp_int_univ.
hint rewrite epdp : valid_epdp_int_univ.

(* univ pair encoding: *)

op [opaque smt_opaque] enc_univ_pair (p : univ * univ) : univ =
  alt true p.`1 ++ [false] ++ p.`2.

op [opaque smt_opaque] dec_univ_pair (u : univ) : (univ * univ) option =
  match de_alt true u with
  | None   => None
  | Some p =>
      if p.`2 = [] then None else Some (p.`1, behead p.`2)
  end.

op [opaque smt_opaque] epdp_univ_pair_univ : (univ * univ, univ) epdp =
  {|enc = enc_univ_pair; dec = dec_univ_pair|}.

lemma valid_epdp_univ_pair_univ : valid_epdp epdp_univ_pair_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_pair_univ /= /enc_univ_pair /dec_univ_pair.
rewrite -catA alt_de_alt //=.
by case x.
rewrite /epdp_univ_pair_univ /= /enc_univ_pair /dec_univ_pair
  => match_eq_some.
have [b val_u] : exists b, de_alt true u = Some (x.`1, [b] ++ x.`2).
  move : match_eq_some.
  case (de_alt true u) => [// | [xs ys] /=].
  case (ys = []) => [// | ys_ne_nil /= <- /=].
  exists (head true ys); by rewrite head_behead.
have := de_alt_alt true u x.`1 ([b] ++ x.`2) _ => //=.
rewrite eqT => [[-> ->]].
by rewrite -!catA cat1s.
qed.

hint simplify valid_epdp_univ_pair_univ.
hint rewrite epdp : valid_epdp_univ_pair_univ.

lemma enc_univ_pair_size_lt1 (x y : univ) :
  size x < size (epdp_univ_pair_univ.`enc (x, y)).
proof.
rewrite /epdp_univ_pair_univ /= /enc_univ_pair !size_cat /=.
rewrite alt_size mulzC -intmulz mulr2z -!addrA ltr_addl.
rewrite ltr_spaddr 1:ltr_spaddl // !size_ge0.
qed.
  
lemma enc_univ_pair_size_lt2 (x y : univ) :
  size y < size (epdp_univ_pair_univ.`enc (x, y)).
proof.
rewrite /epdp_univ_pair_univ /= /enc_univ_pair !size_cat /=.
rewrite alt_size mulzC -intmulz mulr2z addzC.
rewrite ltr_addl ltr_spaddr // ler_paddr !size_ge0.
qed.

lemma enc_univ_pair_nonnil (x y : univ) :
  epdp_univ_pair_univ.`enc (x, y) <> [].
proof.
rewrite /epdp_univ_pair_univ /= /enc_univ_pair.
case (alt true (x, y).`1 ++ [false] ++ (x, y).`2 = []) =>
  [contrad | //].
have size_contrad : size (alt true x ++ [false] ++ y) = 0 by rewrite contrad.
rewrite !size_cat /= paddr_eq0 1:ler_paddr //
        paddr_eq0 1:size_ge0 // in size_contrad.
qed.

(* univ choice encoding: *)

op [opaque smt_opaque] enc_univ_choice (c : (univ, univ) choice) : univ =
  match c with
  | ChoiceLeft u  => true  :: u
  | ChoiceRight u => false :: u
  end.

op [opaque smt_opaque] dec_univ_choice (u : univ) : (univ, univ) choice option =
  if u = []
    then None
  else if head true u
    then Some (ChoiceLeft (behead u))
  else Some (ChoiceRight (behead u)).

op [opaque smt_opaque] epdp_univ_choice_univ : ((univ, univ) choice, univ) epdp =
  {|enc = enc_univ_choice; dec = dec_univ_choice|}.

lemma valid_epdp_univ_choice_univ : valid_epdp epdp_univ_choice_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice_univ /= /enc_univ_choice /dec_univ_choice.
by case x.
rewrite /epdp_univ_choice_univ /= /enc_univ_choice /dec_univ_choice.
case u => [// | y ys /=].
by case y.
qed.

hint simplify valid_epdp_univ_choice_univ.
hint rewrite epdp : valid_epdp_univ_choice_univ.

(* univ choice3 encoding: *)

op choice3_tag_size = 2.
op choice3_tag_1    = [false; false].
op choice3_tag_2    = [false; true].
op choice3_tag_3    = [true;  false].

op [opaque smt_opaque] enc_univ_choice3 (c : (univ, univ, univ) choice3) : univ =
  match c with
  | Choice3_1 u => choice3_tag_1 ++ u
  | Choice3_2 u => choice3_tag_2 ++ u
  | Choice3_3 u => choice3_tag_3 ++ u
  end.

op [opaque smt_opaque] dec_univ_choice3 (u : univ)
     : (univ, univ, univ) choice3 option =
  if size u < choice3_tag_size
  then None
  else let tag  = take 2 u in
       let rest = drop 2 u in
       if tag = choice3_tag_1
         then Some (Choice3_1 rest)
       else if tag = choice3_tag_2
         then Some (Choice3_2 rest)
       else if tag = choice3_tag_3
         then Some (Choice3_3 rest)
       else None.

op [opaque smt_opaque] epdp_univ_choice3_univ
     : ((univ, univ, univ) choice3, univ) epdp =
  {|enc = enc_univ_choice3; dec = dec_univ_choice3|}.

lemma valid_epdp_univ_choice3_univ : valid_epdp epdp_univ_choice3_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice3_univ /= /enc_univ_choice3 /dec_univ_choice3.
case x => /= x.
rewrite /choice3_tag_1 /choice3_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice3_tag_2 /choice3_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice3_tag_3 /choice3_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /epdp_univ_choice3_univ /= /enc_univ_choice3 /dec_univ_choice3.
case (size u < choice3_tag_size) => [// |].
rewrite -lerNgt /choice3_tag_size => ge2_size_u /=.
case x => x.
case (take 2 u = choice3_tag_1) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 2 u = choice3_tag_2) => [// | _].
by case (take 2 u = choice3_tag_3).
case (take 2 u = choice3_tag_1) => [// | _].
case (take 2 u = choice3_tag_2) => [<- /= <- | _].
by rewrite cat_take_drop.
by case (take 2 u = choice3_tag_3).
case (take 2 u = choice3_tag_1) => [// | _].
case (take 2 u = choice3_tag_2) => [// | _].
case (take 2 u = choice3_tag_3) => [<- /= <- | //].
by rewrite cat_take_drop.
qed.

hint simplify valid_epdp_univ_choice3_univ.
hint rewrite epdp : valid_epdp_univ_choice3_univ.

(* univ choice4 encoding: *)

op choice4_tag_size = 2.
op choice4_tag_1    = [false; false].
op choice4_tag_2    = [false; true].
op choice4_tag_3    = [true;  false].
op choice4_tag_4    = [true;  true].

op [opaque smt_opaque] enc_univ_choice4 (c : (univ, univ, univ, univ) choice4)
     : univ =
  match c with
  | Choice4_1 u => choice4_tag_1 ++ u
  | Choice4_2 u => choice4_tag_2 ++ u
  | Choice4_3 u => choice4_tag_3 ++ u
  | Choice4_4 u => choice4_tag_4 ++ u
  end.

op [opaque smt_opaque] dec_univ_choice4 (u : univ)
     : (univ, univ, univ, univ) choice4 option =
  if size u < choice4_tag_size
  then None
  else let tag  = take 2 u in
       let rest = drop 2 u in
       if tag = choice4_tag_1
         then Some (Choice4_1 rest)
       else if tag = choice4_tag_2
         then Some (Choice4_2 rest)
       else if tag = choice4_tag_3
         then Some (Choice4_3 rest)
       else if tag = choice4_tag_4
         then Some (Choice4_4 rest)
       else None.

op [opaque smt_opaque] epdp_univ_choice4_univ
     : ((univ, univ, univ, univ) choice4, univ) epdp =
  {|enc = enc_univ_choice4; dec = dec_univ_choice4|}.

lemma valid_epdp_univ_choice4_univ : valid_epdp epdp_univ_choice4_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice4_univ /= /enc_univ_choice4 /dec_univ_choice4.
case x => /= x.
rewrite /choice4_tag_1 /choice4_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice4_tag_2 /choice4_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice4_tag_3 /choice4_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice4_tag_4 /choice4_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /epdp_univ_choice4_univ /= /enc_univ_choice4 /dec_univ_choice4.
case (size u < choice4_tag_size) => [// |].
rewrite -lerNgt /choice4_tag_size => ge2_size_u /=.
case x => x.
case (take 2 u = choice4_tag_1) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 2 u = choice4_tag_2) => [// | _].
case (take 2 u = choice4_tag_3) => [// | _].
by case (take 2 u = choice4_tag_4).
case (take 2 u = choice4_tag_1) => [// | _].
case (take 2 u = choice4_tag_2) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 2 u = choice4_tag_3) => [// | _].
by case (take 2 u = choice4_tag_4).
case (take 2 u = choice4_tag_1) => [// | _].
case (take 2 u = choice4_tag_2) => [// | _].
case (take 2 u = choice4_tag_3) => [<- /= <- | _].
by rewrite cat_take_drop.
by case (take 2 u = choice4_tag_4).
case (take 2 u = choice4_tag_1) => [// | _].
case (take 2 u = choice4_tag_2) => [// | _].
case (take 2 u = choice4_tag_3) => [// | _].
case (take 2 u = choice4_tag_4) => [<- /= <- | //].
by rewrite cat_take_drop.
qed.

hint simplify valid_epdp_univ_choice4_univ.
hint rewrite epdp : valid_epdp_univ_choice4_univ.

(* univ choice5 encoding: *)

op choice5_tag_size = 3.
op choice5_tag_1    = [false; false; false].
op choice5_tag_2    = [false; false; true].
op choice5_tag_3    = [false; true;  false].
op choice5_tag_4    = [false; true;  true].
op choice5_tag_5    = [true;  false; false].

op [opaque smt_opaque] enc_univ_choice5
     (c : (univ, univ, univ, univ, univ) choice5) : univ =
  match c with
  | Choice5_1 u => choice5_tag_1 ++ u
  | Choice5_2 u => choice5_tag_2 ++ u
  | Choice5_3 u => choice5_tag_3 ++ u
  | Choice5_4 u => choice5_tag_4 ++ u
  | Choice5_5 u => choice5_tag_5 ++ u
  end.

op [opaque smt_opaque] dec_univ_choice5 (u : univ)
     : (univ, univ, univ, univ, univ) choice5 option =
  if size u < choice5_tag_size
  then None
  else let tag  = take 3 u in
       let rest = drop 3 u in
       if tag = choice5_tag_1
         then Some (Choice5_1 rest)
       else if tag = choice5_tag_2
         then Some (Choice5_2 rest)
       else if tag = choice5_tag_3
         then Some (Choice5_3 rest)
       else if tag = choice5_tag_4
         then Some (Choice5_4 rest)
       else if tag = choice5_tag_5
         then Some (Choice5_5 rest)
       else None.

op [opaque smt_opaque] epdp_univ_choice5_univ
     : ((univ, univ, univ, univ, univ) choice5, univ) epdp =
  {|enc = enc_univ_choice5; dec = dec_univ_choice5|}.

lemma valid_epdp_univ_choice5_univ : valid_epdp epdp_univ_choice5_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice5_univ /= /enc_univ_choice5 /dec_univ_choice5.
case x => /= x.
rewrite /choice5_tag_1 /choice5_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice5_tag_2 /choice5_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice5_tag_3 /choice5_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice5_tag_4 /choice5_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice5_tag_5 /choice5_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /epdp_univ_choice5_univ /= /enc_univ_choice5 /dec_univ_choice5.
case (size u < choice5_tag_size) => [// |].
rewrite -lerNgt /choice5_tag_size => ge2_size_u /=.
case x => x.
case (take 3 u = choice5_tag_1) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice5_tag_2) => [// | _].
case (take 3 u = choice5_tag_3) => [// | _].
case (take 3 u = choice5_tag_4) => [// | _].
by case (take 3 u = choice5_tag_5).
case (take 3 u = choice5_tag_1) => [// | _].
case (take 3 u = choice5_tag_2) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice5_tag_3) => [// | _].
case (take 3 u = choice5_tag_4) => [// | _].
by case (take 3 u = choice5_tag_5).
case (take 3 u = choice5_tag_1) => [// | _].
case (take 3 u = choice5_tag_2) => [// | _].
case (take 3 u = choice5_tag_3) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice5_tag_4) => [// | _].
by case (take 3 u = choice5_tag_5).
case (take 3 u = choice5_tag_1) => [// | _].
case (take 3 u = choice5_tag_2) => [// | _].
case (take 3 u = choice5_tag_3) => [// | _].
case (take 3 u = choice5_tag_4) => [<- /= <- | _].
by rewrite cat_take_drop.
by case (take 3 u = choice5_tag_5).
case (take 3 u = choice5_tag_1) => [// | _].
case (take 3 u = choice5_tag_2) => [// | _].
case (take 3 u = choice5_tag_3) => [// | _].
case (take 3 u = choice5_tag_4) => [// | _].
case (take 3 u = choice5_tag_5) => [<- /= <- | //].
by rewrite cat_take_drop.
qed.

hint simplify valid_epdp_univ_choice5_univ.
hint rewrite epdp : valid_epdp_univ_choice5_univ.

(* univ choice6 encoding: *)

op choice6_tag_size = 3.
op choice6_tag_1    = [false; false; false].
op choice6_tag_2    = [false; false; true].
op choice6_tag_3    = [false; true;  false].
op choice6_tag_4    = [false; true;  true].
op choice6_tag_5    = [true;  false; false].
op choice6_tag_6    = [true;  false; true].

op [opaque smt_opaque] enc_univ_choice6
         (c : (univ, univ, univ, univ, univ, univ) choice6) : univ =
  match c with
  | Choice6_1 u => choice6_tag_1 ++ u
  | Choice6_2 u => choice6_tag_2 ++ u
  | Choice6_3 u => choice6_tag_3 ++ u
  | Choice6_4 u => choice6_tag_4 ++ u
  | Choice6_5 u => choice6_tag_5 ++ u
  | Choice6_6 u => choice6_tag_6 ++ u
  end.

op [opaque smt_opaque] dec_univ_choice6 (u : univ)
     : (univ, univ, univ, univ, univ, univ) choice6 option =
  if size u < choice6_tag_size
  then None
  else let tag  = take 3 u in
       let rest = drop 3 u in
       if tag = choice6_tag_1
         then Some (Choice6_1 rest)
       else if tag = choice6_tag_2
         then Some (Choice6_2 rest)
       else if tag = choice6_tag_3
         then Some (Choice6_3 rest)
       else if tag = choice6_tag_4
         then Some (Choice6_4 rest)
       else if tag = choice6_tag_5
         then Some (Choice6_5 rest)
       else if tag = choice6_tag_6
         then Some (Choice6_6 rest)
       else None.

op [opaque smt_opaque] epdp_univ_choice6_univ
     : ((univ, univ, univ, univ, univ, univ) choice6, univ) epdp =
  {|enc = enc_univ_choice6; dec = dec_univ_choice6|}.

lemma valid_epdp_univ_choice6_univ : valid_epdp epdp_univ_choice6_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice6_univ /= /enc_univ_choice6 /dec_univ_choice6.
case x => /= x.
rewrite /choice6_tag_1 /choice6_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice6_tag_2 /choice6_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice6_tag_3 /choice6_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice6_tag_4 /choice6_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice6_tag_5 /choice6_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice6_tag_6 /choice6_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /epdp_univ_choice6_univ /= /enc_univ_choice6 /dec_univ_choice6.
case (size u < choice6_tag_size) => [// |].
rewrite -lerNgt /choice6_tag_size => ge2_size_u /=.
case x => x.
case (take 3 u = choice6_tag_1) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice6_tag_2) => [// | _].
case (take 3 u = choice6_tag_3) => [// | _].
case (take 3 u = choice6_tag_4) => [// | _].
case (take 3 u = choice6_tag_5) => [// | _].
by case (take 3 u = choice6_tag_6).
case (take 3 u = choice6_tag_1) => [// | _].
case (take 3 u = choice6_tag_2) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice6_tag_3) => [// | _].
case (take 3 u = choice6_tag_4) => [// | _].
case (take 3 u = choice6_tag_5) => [// | _].
by case (take 3 u = choice6_tag_6).
case (take 3 u = choice6_tag_1) => [// | _].
case (take 3 u = choice6_tag_2) => [// | _].
case (take 3 u = choice6_tag_3) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice6_tag_4) => [// | _].
case (take 3 u = choice6_tag_5) => [// | _].
by case (take 3 u = choice6_tag_6).
case (take 3 u = choice6_tag_1) => [// | _].
case (take 3 u = choice6_tag_2) => [// | _].
case (take 3 u = choice6_tag_3) => [// | _].
case (take 3 u = choice6_tag_4) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice6_tag_5) => [// | _].
by case (take 3 u = choice6_tag_6).
case (take 3 u = choice6_tag_1) => [// | _].
case (take 3 u = choice6_tag_2) => [// | _].
case (take 3 u = choice6_tag_3) => [// | _].
case (take 3 u = choice6_tag_4) => [// | _].
case (take 3 u = choice6_tag_5) => [<- /= <- | _].
by rewrite cat_take_drop.
by case (take 3 u = choice6_tag_6).
case (take 3 u = choice6_tag_1) => [// | _].
case (take 3 u = choice6_tag_2) => [// | _].
case (take 3 u = choice6_tag_3) => [// | _].
case (take 3 u = choice6_tag_4) => [// | _].
case (take 3 u = choice6_tag_5) => [// | _].
case (take 3 u = choice6_tag_6) => [<- /= <- | //].
by rewrite cat_take_drop.
qed.

hint simplify valid_epdp_univ_choice6_univ.
hint rewrite epdp : valid_epdp_univ_choice6_univ.

(* univ choice7 encoding: *)

op choice7_tag_size = 3.
op choice7_tag_1    = [false; false; false].
op choice7_tag_2    = [false; false; true].
op choice7_tag_3    = [false; true;  false].
op choice7_tag_4    = [false; true;  true].
op choice7_tag_5    = [true;  false; false].
op choice7_tag_6    = [true;  false; true].
op choice7_tag_7    = [true;  true;  false].

op [opaque smt_opaque] enc_univ_choice7
     (c : (univ, univ, univ, univ, univ, univ, univ) choice7) : univ =
  match c with
  | Choice7_1 u => choice7_tag_1 ++ u
  | Choice7_2 u => choice7_tag_2 ++ u
  | Choice7_3 u => choice7_tag_3 ++ u
  | Choice7_4 u => choice7_tag_4 ++ u
  | Choice7_5 u => choice7_tag_5 ++ u
  | Choice7_6 u => choice7_tag_6 ++ u
  | Choice7_7 u => choice7_tag_7 ++ u
  end.

op [opaque smt_opaque] dec_univ_choice7 (u : univ)
     : (univ, univ, univ, univ, univ, univ, univ) choice7 option =
  if size u < choice7_tag_size
  then None
  else let tag  = take 3 u in
       let rest = drop 3 u in
       if tag = choice7_tag_1
         then Some (Choice7_1 rest)
       else if tag = choice7_tag_2
         then Some (Choice7_2 rest)
       else if tag = choice7_tag_3
         then Some (Choice7_3 rest)
       else if tag = choice7_tag_4
         then Some (Choice7_4 rest)
       else if tag = choice7_tag_5
         then Some (Choice7_5 rest)
       else if tag = choice7_tag_6
         then Some (Choice7_6 rest)
       else if tag = choice7_tag_7
         then Some (Choice7_7 rest)
       else None.

op [opaque smt_opaque] epdp_univ_choice7_univ
     : ((univ, univ, univ, univ, univ, univ, univ) choice7, univ) epdp =
  {|enc = enc_univ_choice7; dec = dec_univ_choice7|}.

lemma valid_epdp_univ_choice7_univ : valid_epdp epdp_univ_choice7_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice7_univ /= /enc_univ_choice7 /dec_univ_choice7.
case x => /= x.
rewrite /choice7_tag_1 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice7_tag_2 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice7_tag_3 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice7_tag_4 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice7_tag_5 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice7_tag_6 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice7_tag_7 /choice7_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /epdp_univ_choice7_univ /= /enc_univ_choice7 /dec_univ_choice7.
case (size u < choice7_tag_size) => [// |].
rewrite -lerNgt /choice7_tag_size => ge2_size_u /=.
case x => x.
case (take 3 u = choice7_tag_1) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice7_tag_2) => [// | _].
case (take 3 u = choice7_tag_3) => [// | _].
case (take 3 u = choice7_tag_4) => [// | _].
case (take 3 u = choice7_tag_5) => [// | _].
case (take 3 u = choice7_tag_6) => [// | _].
by case (take 3 u = choice7_tag_7).
case (take 3 u = choice7_tag_1) => [// | _].
case (take 3 u = choice7_tag_2) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice7_tag_3) => [// | _].
case (take 3 u = choice7_tag_4) => [// | _].
case (take 3 u = choice7_tag_5) => [// | _].
case (take 3 u = choice7_tag_6) => [// | _].
by case (take 3 u = choice7_tag_7).
case (take 3 u = choice7_tag_1) => [// | _].
case (take 3 u = choice7_tag_2) => [// | _].
case (take 3 u = choice7_tag_3) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice7_tag_4) => [// | _].
case (take 3 u = choice7_tag_5) => [// | _].
case (take 3 u = choice7_tag_6) => [// | _].
by case (take 3 u = choice7_tag_7).
case (take 3 u = choice7_tag_1) => [// | _].
case (take 3 u = choice7_tag_2) => [// | _].
case (take 3 u = choice7_tag_3) => [// | _].
case (take 3 u = choice7_tag_4) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice7_tag_5) => [// | _].
case (take 3 u = choice7_tag_6) => [// | _].
by case (take 3 u = choice7_tag_7).
case (take 3 u = choice7_tag_1) => [// | _].
case (take 3 u = choice7_tag_2) => [// | _].
case (take 3 u = choice7_tag_3) => [// | _].
case (take 3 u = choice7_tag_4) => [// | _].
case (take 3 u = choice7_tag_5) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice7_tag_6) => [// | _].
by case (take 3 u = choice7_tag_7).
case (take 3 u = choice7_tag_1) => [// | _].
case (take 3 u = choice7_tag_2) => [// | _].
case (take 3 u = choice7_tag_3) => [// | _].
case (take 3 u = choice7_tag_4) => [// | _].
case (take 3 u = choice7_tag_5) => [// | _].
case (take 3 u = choice7_tag_6) => [<- /= <- | _].
by rewrite cat_take_drop.
by case (take 3 u = choice7_tag_7).
case (take 3 u = choice7_tag_1) => [// | _].
case (take 3 u = choice7_tag_2) => [// | _].
case (take 3 u = choice7_tag_3) => [// | _].
case (take 3 u = choice7_tag_4) => [// | _].
case (take 3 u = choice7_tag_5) => [// | _].
case (take 3 u = choice7_tag_6) => [// | _].
case (take 3 u = choice7_tag_7) => [<- /= <- | //].
by rewrite cat_take_drop.
qed.

hint simplify valid_epdp_univ_choice7_univ.
hint rewrite epdp : valid_epdp_univ_choice7_univ.

(* univ choice8 encoding: *)

op choice8_tag_size = 3.
op choice8_tag_1    = [false; false; false].
op choice8_tag_2    = [false; false; true].
op choice8_tag_3    = [false; true;  false].
op choice8_tag_4    = [false; true;  true].
op choice8_tag_5    = [true;  false; false].
op choice8_tag_6    = [true;  false; true].
op choice8_tag_7    = [true;  true;  false].
op choice8_tag_8    = [true;  true;  true].

op [opaque smt_opaque] enc_univ_choice8
     (c : (univ, univ, univ, univ, univ, univ, univ, univ)
      choice8) : univ =
  match c with
  | Choice8_1 u => choice8_tag_1 ++ u
  | Choice8_2 u => choice8_tag_2 ++ u
  | Choice8_3 u => choice8_tag_3 ++ u
  | Choice8_4 u => choice8_tag_4 ++ u
  | Choice8_5 u => choice8_tag_5 ++ u
  | Choice8_6 u => choice8_tag_6 ++ u
  | Choice8_7 u => choice8_tag_7 ++ u
  | Choice8_8 u => choice8_tag_8 ++ u
  end.

op [opaque smt_opaque] dec_univ_choice8 (u : univ)
     : (univ, univ, univ, univ, univ, univ, univ, univ) choice8 option =
  if size u < choice8_tag_size
  then None
  else let tag  = take 3 u in
       let rest = drop 3 u in
       if tag = choice8_tag_1
         then Some (Choice8_1 rest)
       else if tag = choice8_tag_2
         then Some (Choice8_2 rest)
       else if tag = choice8_tag_3
         then Some (Choice8_3 rest)
       else if tag = choice8_tag_4
         then Some (Choice8_4 rest)
       else if tag = choice8_tag_5
         then Some (Choice8_5 rest)
       else if tag = choice8_tag_6
         then Some (Choice8_6 rest)
       else if tag = choice8_tag_7
         then Some (Choice8_7 rest)
       else if tag = choice8_tag_8
         then Some (Choice8_8 rest)
       else None.

op [opaque smt_opaque] epdp_univ_choice8_univ
     : ((univ, univ, univ, univ, univ, univ, univ, univ) choice8, univ)
       epdp =
  {|enc = enc_univ_choice8; dec = dec_univ_choice8|}.

lemma valid_epdp_univ_choice8_univ : valid_epdp epdp_univ_choice8_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_choice8_univ /= /enc_univ_choice8 /dec_univ_choice8.
case x => /= x.
rewrite /choice8_tag_1 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_2 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_3 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_4 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_5 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_6 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_7 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /choice8_tag_8 /choice8_tag_size size_cat /= gtr_addl.
have -> /= : ! size x < 0 by rewrite -lerNgt size_ge0.
by rewrite take0 /= drop0.
rewrite /epdp_univ_choice8_univ /= /enc_univ_choice8 /dec_univ_choice8.
case (size u < choice8_tag_size) => [// |].
rewrite -lerNgt /choice8_tag_size => ge2_size_u /=.
case x => x.
case (take 3 u = choice8_tag_1) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [// | _].
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [// | _].
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [// | _].
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [// | _].
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [// | _].
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [<- /= <- | _].
by rewrite cat_take_drop.
case (take 3 u = choice8_tag_7) => [// | _].
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [<- /= <- | _].
by rewrite cat_take_drop.
by case (take 3 u = choice8_tag_8).
case (take 3 u = choice8_tag_1) => [// | _].
case (take 3 u = choice8_tag_2) => [// | _].
case (take 3 u = choice8_tag_3) => [// | _].
case (take 3 u = choice8_tag_4) => [// | _].
case (take 3 u = choice8_tag_5) => [// | _].
case (take 3 u = choice8_tag_6) => [// | _].
case (take 3 u = choice8_tag_7) => [// | _].
case (take 3 u = choice8_tag_8) => [<- /= <- | //].
by rewrite cat_take_drop.
qed.

hint simplify valid_epdp_univ_choice8_univ.
hint rewrite epdp : valid_epdp_univ_choice8_univ.

(* univ option encoding: *)

op [opaque smt_opaque] enc_univ_option (u_opt : univ option) : univ =
  match u_opt with
  | None   => [true]
  | Some u => false :: u
  end.

op [opaque smt_opaque] dec_univ_option (u : univ) : univ option option =
  if u = []
    then None
  else if head true u
    then if behead u = []
         then Some None
         else None
  else Some (Some (behead u)).

op [opaque smt_opaque] epdp_univ_option_univ : (univ option, univ) epdp =
  {|enc = enc_univ_option; dec = dec_univ_option|}.

lemma valid_epdp_univ_option_univ : valid_epdp epdp_univ_option_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_option_univ /= /enc_univ_option /dec_univ_option.
by case x.
rewrite /epdp_univ_option_univ /= /enc_univ_option /dec_univ_option.
case u => [// | y ys /=].
case y => [_ | _ /= <- //].
case (ys = []) => [-> /= <- // | //].
qed.

hint simplify valid_epdp_univ_option_univ.
hint rewrite epdp : valid_epdp_univ_option_univ.

(* univ list encoding: *)

op [opaque smt_opaque] enc_univ_list (us : univ list) : univ =
  with us = []      => []
  with us = v :: vs => epdp_univ_pair_univ.`enc (v, enc_univ_list vs).

(* we need to use well-founded recursion on the size of lists when
   doing decoding *)

op lt_list_size : 'a list rel = wf_pre size lt_nat.

lemma wf_lt_list_size ['a] : wf lt_list_size<:'a>.
proof.
rewrite wf_pre wf_lt_nat.
qed.

lemma lt_list_sizeP (xs ys : 'a list) :
  lt_list_size xs ys <=> size xs < size ys.
proof.
by rewrite /lt_list_size /wf_pre /lt_nat size_ge0.
qed.

op dec_univ_list_wf_rec_def
   (u : univ, f : univ -> univ list option) : univ list option =
  if u = []
  then Some []
  else match epdp_univ_pair_univ.`dec u with
       | None   => None
       | Some p =>
           match f p.`2 with
           | None    => None
           | Some vs => Some (p.`1 :: vs)
           end
       end.

op dec_univ_list : univ -> univ list option =
  wf_recur lt_list_size None dec_univ_list_wf_rec_def.

op [opaque smt_opaque] epdp_univ_list_univ : (univ list, univ) epdp =
  {|enc = enc_univ_list; dec = dec_univ_list|}.

lemma valid_epdp_univ_list_univ : valid_epdp epdp_univ_list_univ.
proof.
apply epdp_intro => [x |].
rewrite /epdp_univ_list_univ /= /enc_univ_list /dec_univ_list.
elim x => [| x xs IH].
by rewrite wf_recur 1:wf_lt_list_size /= /dec_univ_list_wf_rec_def.
rewrite wf_recur 1:wf_lt_list_size /= {1}/dec_univ_list_wf_rec_def
        enc_univ_pair_nonnil /=.
have -> /= :
  lt_list_size
  (enc_univ_list xs)
  (epdp_univ_pair_univ.`enc (x, enc_univ_list xs)).
  rewrite lt_list_sizeP enc_univ_pair_size_lt2.
by rewrite IH.
apply (wf_ind lt_list_size _).
rewrite wf_lt_list_size.
(* dec part *)
rewrite /epdp_univ_list_univ /=.
move => u IH xs.
rewrite /dec_univ_list wf_recur 1:wf_lt_list_size.
rewrite {1}/dec_univ_list_wf_rec_def.
case (u = []) => [-> /= <- // | nonemp_u].
move => match_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (head witness xs, enc_univ_list (behead xs)).
  move : match_some.
  case (epdp_univ_pair_univ.`dec u) => [// | [x y] /=].
  case (lt_list_size y u) => [lt_list_size_y_u | //]. 
  case
    (wf_recur lt_list_size None
     dec_univ_list_wf_rec_def y = None) =>
      [-> // | /some_oget recur_y_eq].
  rewrite recur_y_eq /= => <- /=.
  rewrite /dec_univ_list in IH.
  by rewrite (IH y).
move : match_some.
rewrite val_u /=.
have <- :
  epdp_univ_pair_univ.`enc
  (head witness xs, enc_univ_list (behead xs)) = u.
  by apply epdp_dec_enc.
have -> /= :
  lt_list_size
  (enc_univ_list (behead xs))
  (epdp_univ_pair_univ.`enc
   (head witness xs, enc_univ_list (behead xs))).
  rewrite lt_list_sizeP enc_univ_pair_size_lt2.
case (wf_recur lt_list_size None dec_univ_list_wf_rec_def
      (enc_univ_list (behead xs)) = None) =>
       [-> // | /some_oget -> /= <- //].
qed.

hint simplify valid_epdp_univ_list_univ.
hint rewrite epdp : valid_epdp_univ_list_univ.

(* tuple3 univ encoding: *)

op [opaque smt_opaque] enc_univ_tuple3 (t : univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc (t.`1, (epdp_univ_pair_univ.`enc (t.`2, t.`3))).

op [opaque smt_opaque] dec_univ_tuple3 (u : univ) : (univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_pair_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2)
      end
  end.

op [opaque smt_opaque] epdp_univ_tuple3_univ : (univ * univ * univ, univ) epdp =
  {|enc = enc_univ_tuple3; dec = dec_univ_tuple3|}.

lemma valid_epdp_univ_tuple3_univ : valid_epdp epdp_univ_tuple3_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_tuple3_univ /= /enc_univ_tuple3 /dec_univ_tuple3 /=.
by case x.
rewrite /epdp_univ_tuple3_univ /= /enc_univ_tuple3 /dec_univ_tuple3 =>
  match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_pair_univ.`enc (x.`2, x.`3)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_pair_univ.`dec q = Some (x.`2, x.`3).
    move : match_dec_q_eq_some.
    case (epdp_univ_pair_univ.`dec q) => // [[]] x2 x3 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_pair_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify valid_epdp_univ_tuple3_univ.
hint rewrite epdp : valid_epdp_univ_tuple3_univ.

(* tuple4 univ encoding: *)

op [opaque smt_opaque] enc_univ_tuple4 (t : univ * univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_tuple3_univ.`enc (t.`2, t.`3, t.`4))).

op [opaque smt_opaque] dec_univ_tuple4
     (u : univ) : (univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_tuple3_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3)
      end
  end.

op [opaque smt_opaque] epdp_univ_tuple4_univ
     : (univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_tuple4; dec = dec_univ_tuple4|}.

lemma valid_epdp_univ_tuple4_univ : valid_epdp epdp_univ_tuple4_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_tuple4_univ /= /enc_univ_tuple4 /dec_univ_tuple4 /=.
by case x.
rewrite /epdp_univ_tuple4_univ /= /enc_univ_tuple4 /dec_univ_tuple4 =>
  match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_tuple3_univ.`enc (x.`2, x.`3, x.`4)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_tuple3_univ.`dec q = Some (x.`2, x.`3, x.`4).
    move : match_dec_q_eq_some.
    case (epdp_univ_tuple3_univ.`dec q) => // [[]] x2 x3 x4 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_tuple3_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify valid_epdp_univ_tuple4_univ.
hint rewrite epdp : valid_epdp_univ_tuple4_univ.

(* tuple5 univ encoding: *)

op [opaque smt_opaque] enc_univ_tuple5 (t : univ * univ * univ * univ * univ)
     : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_tuple4_univ.`enc (t.`2, t.`3, t.`4, t.`5))).

op [opaque smt_opaque] dec_univ_tuple5 (u : univ) :
    (univ * univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_tuple4_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3, q.`4)
      end
  end.

op [opaque smt_opaque] epdp_univ_tuple5_univ :
     (univ * univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_tuple5; dec = dec_univ_tuple5|}.

lemma valid_epdp_univ_tuple5_univ : valid_epdp epdp_univ_tuple5_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_tuple5_univ /= /enc_univ_tuple5
        /dec_univ_tuple5 /=.
by case x.
rewrite /epdp_univ_tuple5_univ /= /enc_univ_tuple5
        /dec_univ_tuple5 => match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_tuple4_univ.`enc (x.`2, x.`3, x.`4, x.`5)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_tuple4_univ.`dec q = Some (x.`2, x.`3, x.`4, x.`5).
    move : match_dec_q_eq_some.
    case (epdp_univ_tuple4_univ.`dec q) => // [[]] x2 x3 x4 x5 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_tuple4_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify valid_epdp_univ_tuple5_univ.
hint rewrite epdp : valid_epdp_univ_tuple5_univ.

(* tuple6 univ encoding: *)

op [opaque smt_opaque] enc_univ_tuple6
     (t : univ * univ * univ * univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_tuple5_univ.`enc (t.`2, t.`3, t.`4, t.`5, t.`6))).

op [opaque smt_opaque] dec_univ_tuple6 (u : univ) :
    (univ * univ * univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_tuple5_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3, q.`4, q.`5)
      end
  end.

op [opaque smt_opaque] epdp_univ_tuple6_univ :
    (univ * univ * univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_tuple6; dec = dec_univ_tuple6|}.

lemma valid_epdp_univ_tuple6_univ : valid_epdp epdp_univ_tuple6_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_tuple6_univ /= /enc_univ_tuple6
        /dec_univ_tuple6 /=.
by case x.
rewrite /epdp_univ_tuple6_univ /= /enc_univ_tuple6
        /dec_univ_tuple6 => match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_tuple5_univ.`enc (x.`2, x.`3, x.`4, x.`5, x.`6)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_tuple5_univ.`dec q = Some (x.`2, x.`3, x.`4, x.`5, x.`6).
    move : match_dec_q_eq_some.
    case (epdp_univ_tuple5_univ.`dec q) => // [[]] x2 x3 x4 x5 x6 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_tuple5_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify valid_epdp_univ_tuple6_univ.
hint rewrite epdp : valid_epdp_univ_tuple6_univ.

(* tuple7 univ encoding: *)

op [opaque smt_opaque] enc_univ_tuple7
     (t : univ * univ * univ * univ * univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_tuple6_univ.`enc (t.`2, t.`3, t.`4, t.`5, t.`6, t.`7))).

op [opaque smt_opaque] dec_univ_tuple7 (u : univ) :
    (univ * univ * univ * univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_tuple6_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3, q.`4, q.`5, q.`6)
      end
  end.

op [opaque smt_opaque] epdp_univ_tuple7_univ :
    (univ * univ * univ * univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_tuple7; dec = dec_univ_tuple7|}.

lemma valid_epdp_univ_tuple7_univ : valid_epdp epdp_univ_tuple7_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_tuple7_univ /= /enc_univ_tuple7
        /dec_univ_tuple7 /=.
by case x.
rewrite /epdp_univ_tuple7_univ /= /enc_univ_tuple7
        /dec_univ_tuple7 => match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_tuple6_univ.`enc (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_tuple6_univ.`dec q = Some (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7).
    move : match_dec_q_eq_some.
    case (epdp_univ_tuple6_univ.`dec q) => // [[]] x2 x3 x4 x5 x6 x7 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_tuple6_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify valid_epdp_univ_tuple7_univ.
hint rewrite epdp : valid_epdp_univ_tuple7_univ.

(* tuple8 univ encoding: *)

op [opaque smt_opaque] enc_univ_tuple8
     (t : univ * univ * univ * univ * univ * univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_tuple7_univ.`enc (t.`2, t.`3, t.`4, t.`5, t.`6, t.`7, t.`8))).

op [opaque smt_opaque] dec_univ_tuple8 (u : univ) :
    (univ * univ * univ * univ * univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_tuple7_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3, q.`4, q.`5, q.`6, q.`7)
      end
  end.

op [opaque smt_opaque] epdp_univ_tuple8_univ :
    (univ * univ * univ * univ * univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_tuple8; dec = dec_univ_tuple8|}.

lemma valid_epdp_univ_tuple8_univ : valid_epdp epdp_univ_tuple8_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_tuple8_univ /= /enc_univ_tuple8
        /dec_univ_tuple8 /=.
by case x.
rewrite /epdp_univ_tuple8_univ /= /enc_univ_tuple8
        /dec_univ_tuple8 => match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some
  (x.`1, epdp_univ_tuple7_univ.`enc (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7, x.`8)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_tuple7_univ.`dec q = Some (x.`2, x.`3, x.`4, x.`5, x.`6, x.`7, x.`8).
    move : match_dec_q_eq_some.
    case (epdp_univ_tuple7_univ.`dec q) => // [[]] x2 x3 x4 x5 x6 x7 x8 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_tuple7_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify valid_epdp_univ_tuple8_univ.
hint rewrite epdp : valid_epdp_univ_tuple8_univ.

(* encoding of pair 'a * 'b *)

op [opaque smt_opaque] epdp_pair_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp)
       : ('a * 'b, univ) epdp =
  epdp_comp epdp_univ_pair_univ (epdp_pair epdp1 epdp2).

lemma valid_epdp_pair_univ (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 =>
  valid_epdp (epdp_pair_univ epdp1 epdp2).
proof.  
move => valid1 valid2.
rewrite /epdp_pair_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_pair_univ.
hint rewrite epdp : valid_epdp_pair_univ.

(* encoding of tuple3 'a * 'b * 'c *)

op [opaque smt_opaque] epdp_tuple3_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp)
       : ('a * 'b * 'c, univ) epdp =
  epdp_comp epdp_univ_tuple3_univ (epdp_tuple3 epdp1 epdp2 epdp3).

lemma valid_epdp_tuple3_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp (epdp_tuple3_univ epdp1 epdp2 epdp3).
proof.  
move => valid1 valid2 valid3.
rewrite /epdp_tuple3_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_tuple3_univ.
hint rewrite epdp : valid_epdp_tuple3_univ.

(* encoding of tuple4 'a * 'b * 'c * 'd *)

op [opaque smt_opaque] epdp_tuple4_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp)
       : ('a * 'b * 'c * 'd, univ) epdp =
  epdp_comp epdp_univ_tuple4_univ (epdp_tuple4 epdp1 epdp2 epdp3 epdp4).

lemma valid_epdp_tuple4_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 =>
  valid_epdp (epdp_tuple4_univ epdp1 epdp2 epdp3 epdp4).
proof.  
move => valid1 valid2 valid3 valid4.
rewrite /epdp_tuple4_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_tuple4_univ.
hint rewrite epdp : valid_epdp_tuple4_univ.

(* encoding of tuple5 'a * 'b * 'c * 'd * 'e *)

op [opaque smt_opaque] epdp_tuple5_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp)
       : ('a * 'b * 'c * 'd * 'e, univ) epdp =
  epdp_comp epdp_univ_tuple5_univ
  (epdp_tuple5 epdp1 epdp2 epdp3 epdp4 epdp5).

lemma valid_epdp_tuple5_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 =>
  valid_epdp (epdp_tuple5_univ epdp1 epdp2 epdp3 epdp4 epdp5).
proof.  
move => valid1 valid2 valid3 valid valid5.
rewrite /epdp_tuple5_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_tuple5_univ.
hint rewrite epdp : valid_epdp_tuple5_univ.

(* encoding of tuple6 'a * 'b * 'c * 'd * 'e * 'f *)

op [opaque smt_opaque] epdp_tuple6_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp)
       : ('a * 'b * 'c * 'd * 'e * 'f, univ) epdp =
  epdp_comp epdp_univ_tuple6_univ
  (epdp_tuple6 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).

lemma valid_epdp_tuple6_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp (epdp_tuple6_univ epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).
proof.  
move => valid1 valid2 valid3 valid valid5 valid6.
rewrite /epdp_tuple6_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_tuple6_univ.
hint rewrite epdp : valid_epdp_tuple6_univ.

(* encoding of tuple7 'a * 'b * 'c * 'd * 'e * 'f * 'g *)

op [opaque smt_opaque] epdp_tuple7_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
      epdp7 : ('g, univ) epdp)
       : ('a * 'b * 'c * 'd * 'e * 'f * 'g, univ) epdp =
  epdp_comp epdp_univ_tuple7_univ
  (epdp_tuple7 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).

lemma valid_epdp_tuple7_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
       epdp7 : ('g, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 =>
  valid_epdp (epdp_tuple7_univ epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).
proof.  
move => valid1 valid2 valid3 valid valid5 valid6 valid7.
rewrite /epdp_tuple7_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_tuple7_univ.
hint rewrite epdp : valid_epdp_tuple7_univ.

(* encoding of tuple8 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h *)

op [opaque smt_opaque] epdp_tuple8_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
      epdp7 : ('g, univ) epdp, epdp8 : ('h, univ) epdp)
       : ('a * 'b * 'c * 'd * 'e * 'f * 'g * 'h, univ) epdp =
  epdp_comp epdp_univ_tuple8_univ
  (epdp_tuple8 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).

lemma valid_epdp_tuple8_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
       epdp7 : ('g, univ) epdp, epdp8 : ('h, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 => valid_epdp epdp8 =>
  valid_epdp
  (epdp_tuple8_univ epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).
proof.  
move => valid1 valid2 valid3 valid valid5 valid6 valid7 valid8.
rewrite /epdp_tuple8_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_tuple8_univ.
hint rewrite epdp : valid_epdp_tuple8_univ.

(* encoding of ('a, 'b) choice *)

op [opaque smt_opaque] epdp_choice_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp)
       : (('a, 'b) choice, univ) epdp =
  epdp_comp epdp_univ_choice_univ (epdp_choice epdp1 epdp2).

lemma valid_epdp_choice_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 =>
  valid_epdp (epdp_choice_univ epdp1 epdp2).
proof.  
move => valid1 valid2.
rewrite /epdp_choice_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice_univ.
hint rewrite epdp : valid_epdp_choice_univ.

(* encoding of ('a, 'b, 'c) choice3 *)

op [opaque smt_opaque] epdp_choice3_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp)
       : (('a, 'b, 'c) choice3, univ) epdp =
  epdp_comp epdp_univ_choice3_univ (epdp_choice3 epdp1 epdp2 epdp3).

lemma valid_epdp_choice3_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('b, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp (epdp_choice3_univ epdp1 epdp2 epdp3).
proof.  
move => valid1 valid2 valid3.
rewrite /epdp_choice3_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice3_univ.
hint rewrite epdp : valid_epdp_choice3_univ.

(* encoding of ('a, 'b, 'c, 'd) choice4 *)

op [opaque smt_opaque] epdp_choice4_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp)
       : (('a, 'b, 'c, 'd) choice4, univ) epdp =
  epdp_comp epdp_univ_choice4_univ (epdp_choice4 epdp1 epdp2 epdp3 epdp4).

lemma valid_epdp_choice4_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('b, univ) epdp, epdp4 : ('d, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 =>
  valid_epdp (epdp_choice4_univ epdp1 epdp2 epdp3 epdp4).
proof.  
move => valid1 valid2 valid3 valid4.
rewrite /epdp_choice4_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice4_univ.
hint rewrite epdp : valid_epdp_choice4_univ.

(* encoding of ('a, 'b, 'c, 'd, 'e) choice5 *)

op [opaque smt_opaque] epdp_choice5_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp)
       : (('a, 'b, 'c, 'd, 'e) choice5, univ) epdp =
  epdp_comp epdp_univ_choice5_univ
  (epdp_choice5 epdp1 epdp2 epdp3 epdp4 epdp5).

lemma valid_epdp_choice5_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('b, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 =>
  valid_epdp (epdp_choice5_univ epdp1 epdp2 epdp3 epdp4 epdp5).
proof.  
move => valid1 valid2 valid3 valid4 valid5.
rewrite /epdp_choice5_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice5_univ.
hint rewrite epdp : valid_epdp_choice5_univ.

(* encoding of ('a, 'b, 'c, 'd, 'e, 'f) choice6 *)

op [opaque smt_opaque] epdp_choice6_univ
   (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
    epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
    epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp)
     : (('a, 'b, 'c, 'd, 'e, 'f) choice6, univ) epdp =
  epdp_comp epdp_univ_choice6_univ
  (epdp_choice6 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).

lemma valid_epdp_choice6_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('b, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp (epdp_choice6_univ epdp1 epdp2 epdp3 epdp4 epdp5 epdp6).
proof.  
move => valid1 valid2 valid3 valid4 valid5 valid6.
rewrite /epdp_choice6_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice6_univ.
hint rewrite epdp : valid_epdp_choice6_univ.

(* encoding of ('a, 'b, 'c, 'd, 'e, 'f, 'g) choice7 *)

op [opaque smt_opaque] epdp_choice7_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
      epdp7 : ('g, univ) epdp)
       : (('a, 'b, 'c, 'd, 'e, 'f, 'g) choice7, univ) epdp =
  epdp_comp epdp_univ_choice7_univ
  (epdp_choice7 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).

lemma valid_epdp_choice7_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('b, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
       epdp7 : ('g, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 =>
  valid_epdp (epdp_choice7_univ epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7).
proof.  
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7.
rewrite /epdp_choice7_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice7_univ.
hint rewrite epdp : valid_epdp_choice7_univ.

(* encoding of ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) choice8 *)

op [opaque smt_opaque] epdp_choice8_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
      epdp7 : ('g, univ) epdp, epdp8 : ('h, univ) epdp)
       : (('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) choice8, univ) epdp =
  epdp_comp epdp_univ_choice8_univ
  (epdp_choice8 epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).

lemma valid_epdp_choice8_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('b, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp, epdp6 : ('f, univ) epdp,
       epdp7 : ('g, univ) epdp, epdp8 : ('h, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 => valid_epdp epdp6 =>
  valid_epdp epdp7 => valid_epdp epdp8 =>
  valid_epdp
  (epdp_choice8_univ epdp1 epdp2 epdp3 epdp4 epdp5 epdp6 epdp7 epdp8).
proof.  
move => valid1 valid2 valid3 valid4 valid5 valid6 valid7 valid8.
rewrite /epdp_choice8_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_choice8_univ.
hint rewrite epdp : valid_epdp_choice8_univ.

(* encoding of 'a option *)

op [opaque smt_opaque] epdp_option_univ
     (epdp : ('a, univ) epdp) : ('a option, univ) epdp =
  epdp_comp epdp_univ_option_univ (epdp_option epdp).

lemma valid_epdp_option_univ (epdp : ('a, univ) epdp) :
  valid_epdp epdp => valid_epdp (epdp_option_univ epdp).
proof.  
move => valid.
rewrite /epdp_option_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_option_univ.
hint rewrite epdp : valid_epdp_option_univ.

(* encoding of 'a list *)

op [opaque smt_opaque] epdp_list_univ
     (epdp : ('a, univ) epdp) : ('a list, univ) epdp =
  epdp_comp epdp_univ_list_univ (epdp_list epdp).

lemma valid_epdp_list_univ (epdp : ('a, univ) epdp) :
  valid_epdp epdp => valid_epdp (epdp_list_univ epdp).
proof.  
move => valid.
rewrite /epdp_list_univ.
by rewrite !epdp.
qed.

hint simplify [reduce] valid_epdp_list_univ.
hint rewrite epdp : valid_epdp_list_univ.
