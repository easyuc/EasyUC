(* Univ.ec *)

(* Universe of Values Plus EPDPs *)

(* TODO
prover [""].  (* no use of SMT provers *)
*)

prover ["Z3" "Alt-Ergo"].  (* TODO - remove! *)

require import AllCore List StdOrder IntDiv BitEncoding UCEncoding WF.
import IntOrder BS2Int.

(* auxiliary definitions and lemmas *)

(* integer logarithms for use below (EasyCrypt now provides these via
   log on reals, but we prefer to work directly with ints) *)

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

(* int2bs, for 1 <= n, with minimum number of bits: *)

op int2bs_min (n : int) : bool list = int2bs (int_log 2 n + 1) n.

lemma div_self (n : int) :
  n <> 0 => n %/ n = 1.
proof.
move => ne0_n.
by rewrite divzz /b2i ne0_n.
qed.

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
rewrite size_ge0.
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

op nosmt enc_unit (x : unit) : univ = [].

op nosmt dec_unit (u : univ) : unit option =
  if u = [] then Some () else None.

op nosmt epdp_unit_univ : (unit, univ) epdp =
  {|enc = enc_unit; dec = dec_unit|}.

lemma valid_epdp_unit_univ : valid_epdp epdp_unit_univ.
apply epdp_intro => [x | u x].
by rewrite /epdp_unit_univ /= /enc_unit /dec_unit.
rewrite /epdp_unit_univ /= /enc_unit /dec_unit.
by case u.
qed.

hint simplify [eqtrue] valid_epdp_unit_univ.
hint rewrite epdp : valid_epdp_unit_univ.

(* bool encoding: *)

op nosmt enc_bool (b : bool) : univ = [b].

op nosmt dec_bool (u : univ) : bool option =
  if size u = 1 then Some (head true u) else None.

op nosmt epdp_bool_univ : (bool, univ) epdp =
  {|enc = enc_bool; dec = dec_bool|}.

lemma valid_epdp_bool_univ : valid_epdp epdp_bool_univ.
apply epdp_intro => [x | u x].
by rewrite /epdp_bool_univ /= /enc_bool /dec_bool.
rewrite /epdp_bool_univ /= /enc_bool /dec_bool.
case u => [// | y ys /=].
case (1 + size ys = 1) => [size_eq /= -> /=| //].
have /= /size_eq0 -> // : (1 + size ys) - 1 = 1 - 1.
  by rewrite size_eq.
qed.

hint simplify [eqtrue] valid_epdp_bool_univ.
hint rewrite epdp : valid_epdp_bool_univ.

(* int encoding: *)

op nosmt enc_int (n : int) : univ =
  if n = 0
  then []
  else if 0 < n
       then true  :: int2bs_min n
       else false :: int2bs_min (-n).

op nosmt dec_int (u : univ) : int option =
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

op nosmt epdp_int_univ : (int, univ) epdp =
  {|enc = enc_int; dec = dec_int|}.

lemma valid_epdp_int_univ : valid_epdp epdp_int_univ.
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

hint simplify [eqtrue] valid_epdp_int_univ.
hint rewrite epdp : valid_epdp_int_univ.

(* univ pair encoding: *)

op nosmt enc_univ_pair (p : univ * univ) : univ =
  alt true p.`1 ++ [false] ++ p.`2.

op nosmt dec_univ_pair (u : univ) : (univ * univ) option =
  match de_alt true u with
  | None   => None
  | Some p =>
      if p.`2 = [] then None else Some (p.`1, behead p.`2)
  end.

op nosmt epdp_univ_pair_univ : (univ * univ, univ) epdp =
  {|enc = enc_univ_pair; dec = dec_univ_pair|}.

lemma valid_epdp_univ_pair_univ : valid_epdp epdp_univ_pair_univ.
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

hint simplify [eqtrue] valid_epdp_univ_pair_univ.
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
have size_contrad :
  size (alt true (x, y).`1 ++ [false] ++ (x, y).`2) = 0.
  by rewrite contrad.
rewrite !size_cat paddr_eq0 1:ler_paddr //
        1:size_ge0 1:size_ge0 in size_contrad.
rewrite paddr_eq0 1:size_ge0 1:size_ge0 // in size_contrad.
qed.

(* univ list encoding: *)

op nosmt enc_univ_list (us : univ list) : univ =
  with us = []      => []
  with us = v :: vs => epdp_univ_pair_univ.`enc (v, enc_univ_list vs).

(* we need to use well-founded recursion on the size of lists when
   doing decoding *)

op lt_list_size : 'a list rel = wf_pre size lt_nat.

lemma wf_list_size ['a] : wf lt_list_size<:'a>.
proof.
rewrite wf_pre wf_lt_nat.
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

op nosmt epdp_univ_list_univ : (univ list, univ) epdp =
  {|enc = enc_univ_list; dec = dec_univ_list|}.

lemma valid_epdp_univ_list_univ : valid_epdp epdp_univ_list_univ.
proof.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_list_univ /= /enc_univ_list /dec_univ_list.
elim x => [| x xs IH].
by rewrite wf_recur 1:wf_list_size /= /dec_univ_list_wf_rec_def.
rewrite wf_recur 1:wf_list_size /= {1}/dec_univ_list_wf_rec_def
        enc_univ_pair_nonnil /=
        epdp_enc_dec 1:valid_epdp_univ_pair_univ /=.
have -> /= :
  predecs lt_list_size
  (epdp_univ_pair_univ.`enc (x, enc_univ_list xs))
  (enc_univ_list xs).
  rewrite /predecs /lt_list_size /wf_pre /lt_nat size_ge0 /=
          enc_univ_pair_size_lt2.
by rewrite IH.
admit.
qed.

hint simplify [eqtrue] valid_epdp_univ_list_univ.
hint rewrite epdp : valid_epdp_univ_list_univ.

(* triple univ encoding: *)

op nosmt enc_univ_triple (t : univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc (t.`1, (epdp_univ_pair_univ.`enc (t.`2, t.`3))).

op nosmt dec_univ_triple (u : univ) : (univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_pair_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2)
      end
  end.

op nosmt epdp_univ_triple_univ : (univ * univ * univ, univ) epdp =
  {|enc = enc_univ_triple; dec = dec_univ_triple|}.

lemma valid_epdp_univ_triple_univ : valid_epdp epdp_univ_triple_univ.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_triple_univ /= /enc_univ_triple /dec_univ_triple.
rewrite !epdp /= !epdp /=.
by case x.
rewrite /epdp_univ_triple_univ /= /enc_univ_triple /dec_univ_triple =>
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

hint simplify [eqtrue] valid_epdp_univ_triple_univ.
hint rewrite epdp : valid_epdp_univ_triple_univ.

(* quadruple univ encoding: *)

op nosmt enc_univ_quadruple (t : univ * univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_triple_univ.`enc (t.`2, t.`3, t.`4))).

op nosmt dec_univ_quadruple (u : univ) : (univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_triple_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3)
      end
  end.

op nosmt epdp_univ_quadruple_univ : (univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_quadruple; dec = dec_univ_quadruple|}.

lemma valid_epdp_univ_quadruple_univ : valid_epdp epdp_univ_quadruple_univ.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_quadruple_univ /= /enc_univ_quadruple /dec_univ_quadruple /=.
rewrite !epdp /= !epdp /=.
by case x.
rewrite /epdp_univ_quadruple_univ /= /enc_univ_quadruple /dec_univ_quadruple =>
  match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_triple_univ.`enc (x.`2, x.`3, x.`4)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_triple_univ.`dec q = Some (x.`2, x.`3, x.`4).
    move : match_dec_q_eq_some.
    case (epdp_univ_triple_univ.`dec q) => // [[]] x2 x3 x4 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_triple_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify [eqtrue] valid_epdp_univ_quadruple_univ.
hint rewrite epdp : valid_epdp_univ_quadruple_univ.

(* quintuple univ encoding: *)

op nosmt enc_univ_quintuple (t : univ * univ * univ * univ * univ) : univ =
  epdp_univ_pair_univ.`enc
  (t.`1, (epdp_univ_quadruple_univ.`enc (t.`2, t.`3, t.`4, t.`5))).

op nosmt dec_univ_quintuple (u : univ) :
    (univ * univ * univ * univ * univ) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp_univ_quadruple_univ.`dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2, q.`3, q.`4)
      end
  end.

op nosmt epdp_univ_quintuple_univ :
    (univ * univ * univ * univ * univ, univ) epdp =
  {|enc = enc_univ_quintuple; dec = dec_univ_quintuple|}.

lemma valid_epdp_univ_quintuple_univ : valid_epdp epdp_univ_quintuple_univ.
apply epdp_intro => [x | u x].
rewrite /epdp_univ_quintuple_univ /= /enc_univ_quintuple
        /dec_univ_quintuple /=.
rewrite !epdp /= !epdp /=.
by case x.
rewrite /epdp_univ_quintuple_univ /= /enc_univ_quintuple
        /dec_univ_quintuple => match_dec_u_eq_some.
have val_u :
  epdp_univ_pair_univ.`dec u =
  Some (x.`1, epdp_univ_quadruple_univ.`enc (x.`2, x.`3, x.`4, x.`5)).
  move : match_dec_u_eq_some.
  case (epdp_univ_pair_univ.`dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    epdp_univ_quadruple_univ.`dec q = Some (x.`2, x.`3, x.`4, x.`5).
    move : match_dec_q_eq_some.
    case (epdp_univ_quadruple_univ.`dec q) => // [[]] x2 x3 x4 x5 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  rewrite (epdp_dec_enc _ _ q) 1:valid_epdp_univ_quadruple_univ //.
by rewrite (epdp_dec_enc _ _ u) 1:valid_epdp_univ_pair_univ.
qed.

hint simplify [eqtrue] valid_epdp_univ_quintuple_univ.
hint rewrite epdp : valid_epdp_univ_quintuple_univ.

(* encoding of 'a * 'b *)

op nosmt enc_pair_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp, p : 'a * 'b) : univ =
  epdp_univ_pair_univ.`enc (epdp1.`enc p.`1, epdp2.`enc p.`2).
  
op nosmt dec_pair_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp, u : univ)
       : ('a * 'b) option =
  match epdp_univ_pair_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp1.`dec p.`1 with
      | None    => None
      | Some x1 =>
          match epdp2.`dec p.`2 with
          | None    => None
          | Some x2 => Some (x1, x2)
          end
      end
  end.

op nosmt epdp_pair_univ (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp)
     : ('a * 'b, univ) epdp =
  {|enc = enc_pair_univ epdp1 epdp2; dec = dec_pair_univ epdp1 epdp2|}.

lemma valid_epdp_pair_univ (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 =>
  valid_epdp (epdp_pair_univ epdp1 epdp2).
proof.  
move => valid1 valid2.
apply epdp_intro => [x | y x].
rewrite /epdp_pair_univ /= /dec_pair_univ /enc_pair_univ.
rewrite !epdp /= !epdp // /=.
by case x.  
rewrite /epdp_pair_univ /= /dec_pair_univ /enc_pair_univ => match_dec_y_eq_some.
have val_y :
  epdp_univ_pair_univ.`dec y = Some (epdp1.`enc x.`1, epdp2.`enc x.`2).
  move : match_dec_y_eq_some.
  case (epdp_univ_pair_univ.`dec y) => // [[]] x1 x2 /=.
  move => match_dec_x1_eq_some.
  have val_x1 : epdp1.`dec x1 = Some x.`1.
    move : match_dec_x1_eq_some.
    case (epdp1.`dec x1) => // x1' /=.
    case (epdp2.`dec x2) => // _ /=.
  rewrite (epdp_dec_enc _ _ x1) //=.
  move : match_dec_x1_eq_some.
  rewrite val_x1 /= => match_dec_x2_eq_some.
  have val_x2 : epdp2.`dec x2 = Some x.`2.
    move : match_dec_x2_eq_some.
    case (epdp2.`dec x2) => // x2' /= <- //.
  rewrite (epdp_dec_enc _ _ x2) //.
by rewrite (epdp_dec_enc _ _ y) 1:valid_epdp_univ_pair_univ.
qed.

hint rewrite epdp_sub : valid_epdp_pair_univ.

(* encoding of 'a * 'b * 'c *)

op nosmt enc_triple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp, epdp3 : ('c, univ) epdp,
      p : 'a * 'b * 'c) : univ =
  epdp_univ_triple_univ.`enc
  (epdp1.`enc p.`1, epdp2.`enc p.`2, epdp3.`enc p.`3).
  
op nosmt dec_triple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, u : univ) : ('a * 'b * 'c) option =
  match epdp_univ_triple_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp1.`dec p.`1 with
      | None    => None
      | Some x1 =>
          match epdp2.`dec p.`2 with
          | None    => None
          | Some x2 =>
              match epdp3.`dec p.`3 with
              | None    => None
              | Some x3 => Some (x1, x2, x3)
              end
          end
      end
  end.

op nosmt epdp_triple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp, epdp3 : ('c, univ) epdp)
       : ('a * 'b * 'c, univ) epdp =
  {|enc = enc_triple_univ epdp1 epdp2 epdp3;
    dec = dec_triple_univ epdp1 epdp2 epdp3|}.

lemma valid_epdp_triple_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp (epdp_triple_univ epdp1 epdp2 epdp3).
proof.  
move => valid1 valid2 valid3.
apply epdp_intro => [x | y x].
rewrite /epdp_triple_univ /= /dec_triple_univ /enc_triple_univ.
rewrite !epdp /= !epdp //=.
by case x.  
rewrite /epdp_triple_univ /= /dec_triple_univ /enc_triple_univ =>
  match_dec_y_eq_some.
have val_y :
  epdp_univ_triple_univ.`dec y =
  Some (epdp1.`enc x.`1, epdp2.`enc x.`2, epdp3.`enc x.`3).
  move : match_dec_y_eq_some.
  case (epdp_univ_triple_univ.`dec y) => // [[]] x1 x2 x3 /=.
  move => match_dec_x1_eq_some.
  have val_x1 : epdp1.`dec x1 = Some x.`1.
    move : match_dec_x1_eq_some.
    case (epdp1.`dec x1) => // x1' /=.
    case (epdp2.`dec x2) => // x0 /=.
    case (epdp3.`dec x3) => // _ /=.
  rewrite (epdp_dec_enc _ _ x1) 1:valid1 //=.
  move : match_dec_x1_eq_some.
  rewrite val_x1 /= => match_dec_x2_eq_some.
  have val_x2 : epdp2.`dec x2 = Some x.`2.
    move : match_dec_x2_eq_some.
    case (epdp2.`dec x2) => // x2' /=.
    by case (epdp3.`dec x3) => // x0 /= <-.
  rewrite (epdp_dec_enc _ _ x2) 1:valid2 //=.
  move : match_dec_x2_eq_some.
  rewrite val_x2 /= => match_dec_x3_eq_some.
  have val_x3 : epdp3.`dec x3 = Some x.`3.
    move : match_dec_x3_eq_some.
    by case (epdp3.`dec x3) => // x3' /= <-.
  rewrite (epdp_dec_enc _ _ x3) //.
by rewrite (epdp_dec_enc _ _ y) 1:valid_epdp_univ_triple_univ.
qed.

hint rewrite epdp_sub : valid_epdp_triple_univ.

(* encoding of 'a * 'b * 'c * 'd *)

op nosmt enc_quadruple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      p : 'a * 'b * 'c * 'd) : univ =
  epdp_univ_quadruple_univ.`enc
  (epdp1.`enc p.`1, epdp2.`enc p.`2, epdp3.`enc p.`3, epdp4.`enc p.`4).
  
op nosmt dec_quadruple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      u : univ) : ('a * 'b * 'c * 'd) option =
  match epdp_univ_quadruple_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp1.`dec p.`1 with
      | None    => None
      | Some x1 =>
          match epdp2.`dec p.`2 with
          | None    => None
          | Some x2 =>
              match epdp3.`dec p.`3 with
              | None    => None
              | Some x3 =>
                  match epdp4.`dec p.`4 with
                  | None    => None
                  | Some x4 => Some (x1, x2, x3, x4)
                  end
              end
          end
      end
  end.

op nosmt epdp_quadruple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp)
       : ('a * 'b * 'c * 'd, univ) epdp =
  {|enc = enc_quadruple_univ epdp1 epdp2 epdp3 epdp4;
    dec = dec_quadruple_univ epdp1 epdp2 epdp3 epdp4|}.

lemma valid_epdp_quadruple_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 =>
  valid_epdp (epdp_quadruple_univ epdp1 epdp2 epdp3 epdp4).
proof.  
move => valid1 valid2 valid3 valid4.
apply epdp_intro => [x | y x].
rewrite /epdp_quadruple_univ /= /dec_quadruple_univ /enc_quadruple_univ.
rewrite !epdp /= !epdp //=.
by case x.  
rewrite /epdp_quadruple_univ /= /dec_quadruple_univ /enc_quadruple_univ =>
  match_dec_y_eq_some.
have val_y :
  epdp_univ_quadruple_univ.`dec y =
  Some (epdp1.`enc x.`1, epdp2.`enc x.`2, epdp3.`enc x.`3, epdp4.`enc x.`4).
  move : match_dec_y_eq_some.
  case (epdp_univ_quadruple_univ.`dec y) => // [[]] x1 x2 x3 x4 /=.
  move => match_dec_x1_eq_some.
  have val_x1 : epdp1.`dec x1 = Some x.`1.
    move : match_dec_x1_eq_some.
    case (epdp1.`dec x1) => // x1' /= match_dec_x2_eq_some.
    have val_x2 : epdp2.`dec x2 = Some x.`2.
      move : match_dec_x2_eq_some.
      case (epdp2.`dec x2) => // x2' /=.
      case (epdp3.`dec x3) => // x0 /=.
      case (epdp4.`dec x4) => // _ /=.
    move : match_dec_x2_eq_some.
    rewrite val_x2 /=.
    case (epdp3.`dec x3) => // x0 /=.
    by case (epdp4.`dec x4) => // x5 /= <-.
  move : match_dec_x1_eq_some.
  rewrite val_x1 => /= match_dec_x2_eq_some.
  rewrite (epdp_dec_enc _ _ x1) //=.
  have val_x2 : epdp2.`dec x2 = Some x.`2. 
    move : match_dec_x2_eq_some.
    case (epdp2.`dec x2) => // x2' /=.
    case (epdp3.`dec x3) => // x0 /=.
    by case (epdp4.`dec x4) => // x5 /= <-.
  rewrite (epdp_dec_enc _ _ x2) //=.
  move : match_dec_x2_eq_some.
  rewrite val_x2 /= => match_dec_x3_eq_some.
  have val_x3 : epdp3.`dec x3 = Some x.`3.
    move : match_dec_x3_eq_some.
    case (epdp3.`dec x3) => // x3' /=.
    by case (epdp4.`dec x4) => // x0 /= <-.
  rewrite (epdp_dec_enc _ _ x3) //=.
  move : match_dec_x3_eq_some.
  rewrite val_x3 /= => match_dec_x4_eq_some.
  have val_x4 : epdp4.`dec x4 = Some x.`4.
    move : match_dec_x4_eq_some.
    by case (epdp4.`dec x4) => // x4' /= <-.
  by rewrite (epdp_dec_enc _ _ x4).
by rewrite (epdp_dec_enc _ _ y) 1:valid_epdp_univ_quadruple_univ.
qed.

hint rewrite epdp_sub : valid_epdp_quadruple_univ.

(* encoding of 'a * 'b * 'c * 'd * 'e *)

op nosmt enc_quintuple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp,
      p : 'a * 'b * 'c * 'd * 'e) : univ =
  epdp_univ_quintuple_univ.`enc
  (epdp1.`enc p.`1, epdp2.`enc p.`2, epdp3.`enc p.`3,
   epdp4.`enc p.`4, epdp5.`enc p.`5).
  
op nosmt dec_quintuple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp,
      u : univ) : ('a * 'b * 'c * 'd * 'e) option =
  match epdp_univ_quintuple_univ.`dec u with
  | None   => None
  | Some p =>
      match epdp1.`dec p.`1 with
      | None    => None
      | Some x1 =>
          match epdp2.`dec p.`2 with
          | None    => None
          | Some x2 =>
              match epdp3.`dec p.`3 with
              | None    => None
              | Some x3 =>
                  match epdp4.`dec p.`4 with
                  | None    => None
                  | Some x4 =>
                      match epdp5.`dec p.`5 with
                      | None    => None
                      | Some x5 => Some (x1, x2, x3, x4, x5)
                      end
                  end
              end
          end
      end
  end.

op nosmt epdp_quintuple_univ
     (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
      epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
      epdp5 : ('e, univ) epdp)
       : ('a * 'b * 'c * 'd * 'e, univ) epdp =
  {|enc = enc_quintuple_univ epdp1 epdp2 epdp3 epdp4 epdp5;
    dec = dec_quintuple_univ epdp1 epdp2 epdp3 epdp4 epdp5|}.

lemma valid_epdp_quintuple_univ
      (epdp1 : ('a, univ) epdp, epdp2 : ('b, univ) epdp,
       epdp3 : ('c, univ) epdp, epdp4 : ('d, univ) epdp,
       epdp5 : ('e, univ) epdp) :
  valid_epdp epdp1 => valid_epdp epdp2 => valid_epdp epdp3 =>
  valid_epdp epdp4 => valid_epdp epdp5 =>
  valid_epdp (epdp_quintuple_univ epdp1 epdp2 epdp3 epdp4 epdp5).
proof.  
move => valid1 valid2 valid3 valid4 valid5.
apply epdp_intro => [x | y x].
rewrite /epdp_quintuple_univ /= /dec_quintuple_univ /enc_quintuple_univ.
rewrite !epdp /= !epdp //=.
by case x.  
rewrite /epdp_quintuple_univ /= /dec_quintuple_univ /enc_quintuple_univ =>
  match_dec_y_eq_some.
have val_y :
  epdp_univ_quintuple_univ.`dec y =
  Some (epdp1.`enc x.`1, epdp2.`enc x.`2, epdp3.`enc x.`3,
        epdp4.`enc x.`4, epdp5.`enc x.`5).
  move : match_dec_y_eq_some.
  case (epdp_univ_quintuple_univ.`dec y) => // [[]] x1 x2 x3 x4 x5 /=.
  move => match_dec_x1_eq_some.
  have val_x1 : epdp1.`dec x1 = Some x.`1.
    move : match_dec_x1_eq_some.
    case (epdp1.`dec x1) => // x1' /= match_dec_x2_eq_some.
    have val_x2 : epdp2.`dec x2 = Some x.`2.
      move : match_dec_x2_eq_some.
      case (epdp2.`dec x2) => // x2' /=.
      case (epdp3.`dec x3) => // x0 /=.
      case (epdp4.`dec x4) => // x6 /=.
      case (epdp5.`dec x5) => // _ /=.
    move : match_dec_x2_eq_some.
    rewrite val_x2 /=.
    case (epdp3.`dec x3) => // x0 /=.
    case (epdp4.`dec x4) => // x6 /=.
    by case (epdp5.`dec x5) => // x7 /= <-.
  move : match_dec_x1_eq_some.
  rewrite val_x1 => /= match_dec_x2_eq_some.
  rewrite (epdp_dec_enc _ _ x1) //=.
  have val_x2 : epdp2.`dec x2 = Some x.`2. 
    move : match_dec_x2_eq_some.
    case (epdp2.`dec x2) => // x2' /=.
    case (epdp3.`dec x3) => // x0 /=.
    case (epdp4.`dec x4) => // x6 /=.
    by case (epdp5.`dec x5) => // x7 /= <-.
  rewrite (epdp_dec_enc _ _ x2) //=.
  move : match_dec_x2_eq_some.
  rewrite val_x2 /= => match_dec_x3_eq_some.
  have val_x3 : epdp3.`dec x3 = Some x.`3.
    move : match_dec_x3_eq_some.
    case (epdp3.`dec x3) => // x3' /=.
    case (epdp4.`dec x4) => // x0 /=.
    by case (epdp5.`dec x5) => // x6 /= <-.
  rewrite (epdp_dec_enc _ _ x3) //=.
  move : match_dec_x3_eq_some.
  rewrite val_x3 /= => match_dec_x4_eq_some.
  have val_x4 : epdp4.`dec x4 = Some x.`4.
    move : match_dec_x4_eq_some.
    case (epdp4.`dec x4) => // x4' /=.
    by case (epdp5.`dec x5) => // x0 /= <-.
  rewrite (epdp_dec_enc _ _ x4) //=.
  move : match_dec_x4_eq_some.
  rewrite val_x4 /= => match_dec_x5_eq_some.
  have val_x5 : epdp5.`dec x5 = Some x.`5.
    move : match_dec_x5_eq_some.
    by case (epdp5.`dec x5) => // x5' /= <-.
  by rewrite (epdp_dec_enc _ _ x5).
by rewrite (epdp_dec_enc _ _ y) 1:valid_epdp_univ_quintuple_univ.
qed.

hint rewrite epdp_sub : valid_epdp_quintuple_univ.

(* encoding of 'a list *)

op nosmt enc_list_univ (epdp : ('a, univ) epdp, xs : 'a list) : univ =
  epdp_univ_list_univ.`enc (map epdp.`enc xs).

op nosmt dec_list_univ
     (epdp : ('a, univ) epdp, u : univ) : 'a list option =
  match epdp_univ_list_univ.`dec u with
    None    => None
  | Some vs =>
      let ys = map epdp.`dec vs
      in if all is_some ys
         then Some (map oget ys)
         else None
  end.

op nosmt epdp_list_univ (epdp : ('a, univ) epdp) : ('a list, univ) epdp =
  {|enc = enc_list_univ epdp; dec = dec_list_univ epdp|}.

lemma valid_epdp_list_univ (epdp : ('a, univ) epdp) :
  valid_epdp epdp => valid_epdp (epdp_list_univ epdp).
proof.  
move => valid.
apply epdp_intro => [xs | y xs].
rewrite /epdp_list_univ /enc_list_univ /dec_list_univ /=.
rewrite !epdp /=.
have -> : map epdp.`dec (map epdp.`enc xs) = map Some xs.
  elim xs => [// | y ys /=].
  rewrite !epdp //.
have -> /= : all is_some (map Some xs) = true.
  elim xs => [// | y ys //].
elim xs => [// | y ys //].
rewrite /epdp_list_univ /enc_list_univ /dec_list_univ /= =>
  match_dec_y_eq_some.
have val_u : epdp_univ_list_univ.`dec y = Some (map epdp.`enc xs).
  move : match_dec_y_eq_some.
  case (epdp_univ_list_univ.`dec y) => // zs /=.
  case (all is_some (map epdp.`dec zs)) => // => all_is_some /= <-.
  move : all_is_some.
  elim zs => [// | w ws IH /= [#] is_some_dec_w all_is_some_dec_ws].
  split.
  rewrite (epdp_dec_enc _ _ w) // -(some_oget (epdp.`dec w)) //.
  move : is_some_dec_w; by case (epdp.`dec w).
  by apply IH.
by rewrite (epdp_dec_enc _ _ y) 1:valid_epdp_univ_list_univ.
qed.

hint rewrite epdp_sub : valid_epdp_list_univ.
