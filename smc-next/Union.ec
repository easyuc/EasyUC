(* Union.ec *)

(* Disjoint Unions *)

type ('a, 'b) union2 =
  [Union2_1 of 'a | Union2_2 of 'b].

type ('a, 'b, 'c) union3 =
  [Union3_1 of 'a | Union3_2 of 'b | Union3_3 of 'c].

type ('a, 'b, 'c, 'd) union4 =
  [Union4_1 of 'a | Union4_2 of 'b | Union4_3 of 'c | Union4_4 of 'd].

