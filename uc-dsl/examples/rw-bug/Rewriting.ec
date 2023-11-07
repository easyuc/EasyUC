require import AllCore List.
require import SmtMap.

(* SmtMap hints *)
hint simplify [reduce] get_setE.

(* List hints *)
hint simplify [reduce] take0, drop0, size_ge0, take_size, cats0, take_size_cat.

lemma plus_size_le_false (n m : int, xs : 'a list) :
  m < n =>
  n + size xs <= m = false.
proof.
smt(size_ge0).
qed.

(*
hint simplify [reduce] plus_size_le_false.
*)

hint rewrite plus_size_le_hints : plus_size_le_false.

op maxUINT8 = nseq 8 true.
op varData : bool list list.

lemma foo (f : bool list list -> bool) :
  f
  (take (2 + size varData)
   (maxUINT8 :: maxUINT8 :: (varData ++ nseq 1024 maxUINT8))).
proof.
simplify.
(*
Current goal

Type variables: <none>

f: bool list list -> bool
------------------------------------------------------------------------
f
  (if 2 + size varData <= 0 then []
   else maxUINT8 :: if 1 + size varData <= 0 then [] else maxUINT8 :: varData)
*)
rewrite !plus_size_le_hints //=.
(*
Current goal

Type variables: <none>

f: bool list list -> bool
------------------------------------------------------------------------
f (maxUINT8 :: maxUINT8 :: varData)
*)
abort.

