(* Aux.ec *)

(* Auxiliary Lemmas *)

prover [""].  (* no provers *)

require import AllCore List.

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
