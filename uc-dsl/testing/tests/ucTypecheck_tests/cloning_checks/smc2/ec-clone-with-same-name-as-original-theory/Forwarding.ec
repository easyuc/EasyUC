op fwd_const = 3.

lemma fwd_const_eq : fwd_const = 3.
proof. by rewrite /fwd_const. qed.

hint simplify [reduce] fwd_const_eq.
