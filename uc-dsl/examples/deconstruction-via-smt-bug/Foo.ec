require import AllCore List.

type 'a my_list = [Nil | Cons of 'a & 'a my_list].

op x : int my_list.

axiom x_ax : x = Cons 3 Nil.

(* these work: *)

lemma foo :
  get_as_Cons x <> None.
proof.
smt(x_ax).
qed.

lemma foo' :
  get_as_Cons x <> None.
proof.
smt.
qed.
