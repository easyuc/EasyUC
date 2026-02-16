uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct A {
in x@bla()
}

direct D {A:A}

functionality A(F1:D,F2:D) implements D {
 party P serves A.A {
  initial state I {match message with * => {fail.} end}
 }
}
