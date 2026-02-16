uc_requires Req.
uc_clone Req as Req1.
uc_clone Req as Req2.

direct A {
in x@bla()
}

direct D {D:A}

functionality R(F1:Req1.D,F2:Req2.D) implements D {
 party P serves D.D {initial state I {match message with * => {fail.}end}}
}
