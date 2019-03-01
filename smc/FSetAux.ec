(* FSetAux.ec *)

(* Auxiliary Lemmas on Finite Sets *)

prover quorum=2 ["Alt-Ergo" "Z3"].  (* both Alt-Ergo and Z3 must succeed *)

require import FSet List.

lemma oflist_cat (xs ys : 'a list) :
  oflist (xs ++ ys) = oflist xs `|` oflist ys.
proof.
apply fsetP => z.
by rewrite mem_oflist mem_cat in_fsetU 2!mem_oflist.
qed.

lemma oflist_cons (x : 'a, ys : 'a list) :
  oflist (x :: ys) = fset1 x `|` oflist ys.
proof. by rewrite -cat1s oflist_cat set1E. qed.

lemma oflist_rcons (x : 'a, ys : 'a list) :
  oflist (rcons ys x) = fset1 x `|` oflist ys.
proof. by rewrite -cats1 oflist_cat set1E fsetUC. qed.

lemma minus1_not_mem (xs : 'a fset, y : 'a) :
  ! mem xs y => xs `\` fset1 y = xs.
proof.
move => not_mem_xs_y.
apply fsetP => x; smt(in_fsetD1).
qed.

lemma subset_union_r (xs ys : 'a fset) :
  xs \subset ys `|` xs.
proof.
rewrite subsetP => z; rewrite in_fsetU => />.
qed.

lemma subset_union_l (xs ys : 'a fset) :
  xs \subset xs `|` ys.
proof.
rewrite subsetP => z; rewrite in_fsetU => />.
qed.
