(* ListAux.ec *)

(* Auxiliary Lemmas on Lists *)

prover quorum=2 ["Alt-Ergo" "Z3"].  (* both Alt-Ergo and Z3 must succeed *)

require import AllCore List.
require import StdOrder. import IntOrder.

lemma nth_in_range (i : int, x y : 'a, zs : 'a list) :
  0 <= i < size zs => nth x zs i = nth y zs i.
proof.
move : i.
elim zs => [/= i [ge0_i lt0_i] | z zs IH i /= [ge0_i lt_sz_zs_plus1]].
have // : 0 < 0 by apply (ler_lt_trans i).
case (i = 0) => // ne0_i; rewrite IH /#.
qed.

lemma nth_head (z : 'a, xs : 'a list) :
  nth z xs 0 = head z xs.
proof.
case (xs = []) => [-> | ne_xs_nil].
by rewrite nth_default.
by rewrite -(head_behead xs z).
qed.

lemma drop1_behead (xs : 'a list) :
  drop 1 xs = behead xs.
proof.
case (xs = []) => [-> // | non_nil_xs].
have <- /= : head witness xs :: behead xs = xs
  by apply head_behead.
by rewrite drop0.
qed.

lemma mem_ne_list_behead (xs : 'a list, y : 'a) :
  xs <> [] =>
  (mem xs y <=>
   y = head witness xs \/ mem (behead xs) y).
proof.
move => non_nil_xs.
split => [mem_xs_y | disj].
by rewrite -in_cons head_behead.
have <- // : head witness xs :: behead xs = xs
  by apply head_behead.
qed.

lemma mem_ne_list_drop1 (xs : 'a list, y : 'a) :
  xs <> [] =>
  (mem xs y <=>
   y = head witness xs \/ mem (drop 1 xs) y).
proof.
move => non_nil_xs.
by rewrite drop1_behead mem_ne_list_behead.
qed.

lemma drop1_drop (xs : 'a list, n : int) :
  0 <= n => drop (n + 1) xs = drop 1 (drop n xs).
proof.
move => ge0_n.
case (n < size xs) => [lt_n_sz_xs | not_lt_n_sz_xs].
by rewrite (drop_nth witness n) //= drop0.
have ge_sz_xs_n : size xs <= n by rewrite lezNgt.
rewrite (drop_oversize n) // (drop_oversize 1) // (drop_oversize (n + 1)) //.
by rewrite (lez_trans n) // -{1}addz0 (lez_add2l n 0 1).
qed.

lemma drop_drop (xs : 'a list, n m : int) :
  0 <= n => 0 <= m =>
  drop (n + m) xs = drop n (drop m xs).
proof.
elim n => [ge0_m /= | n ge0_n IH ge0_m].
by rewrite drop0.
by rewrite (drop1_drop (drop m xs) n) // -IH // -drop1_drop 1:addz_ge0 //
           addzAC.
qed.

lemma nonnil_cat_nonnil_r (xs ys : 'a list) :
  ys <> [] => xs ++ ys <> [].
proof. by elim xs. qed.

lemma nonnil_cat_nonnil_l (xs ys : 'a list) :
  ys <> [] => ys ++ xs <> [].
proof. by elim ys. qed.

lemma ne_cat_nonnil_r (xs ys : 'a list) :
  ys <> [] => xs ++ ys <> xs.
proof. by elim xs. qed.

lemma ne_cat_nonnil_l (xs ys : 'a list) :
  ys <> [] => ys ++ xs <> xs.
proof.
(case xs; first by rewrite cats0) => z zs nonnil_ys.
case (ys ++ z :: zs = z :: zs) => [eq | //].
rewrite -cat1s catA -(cat0s ([z] ++ zs)) -catA in eq.
have // : ys = [] by apply (catIs ys [] ([z] ++ zs)).
qed.
