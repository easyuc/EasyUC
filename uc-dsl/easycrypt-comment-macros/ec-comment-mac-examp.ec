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
