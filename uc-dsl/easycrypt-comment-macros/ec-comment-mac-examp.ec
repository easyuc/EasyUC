(* (* *) *)

(*! Empty() *)

(*! Foo ( A, Bo1, C  )

hi there (* (*! only macro if at top level
(* *)
<<A>> -> <<Bo1>>

 *) <<C>> *)
 *)

(*! Goo
    (A, B )

<<C>>
hi there <<A>>:<<B>>
 *)

(*! Bar(A, B) <<A>> : (*!<<B>>*) <<A>> A *)

(*! SecBound(Path, Adv, Mem)
|Pr[<<Path>>.GRF
    (<<Path>>.PRF,
     <<Path>>.Adv2RFA(<<Adv>>)).main() @ <<Mem>> : res] -
 Pr[<<Path>>.GRF
    (<<Path>>.TRF,
     <<Path>>.Adv2RFA(<<Adv>>)).main() @ <<Mem>> : res]| +
(<<Path>>.limit_pre%r + <<Path>>.limit_post%r) / (2 ^ <<Path>>.text_len)%r
*)
