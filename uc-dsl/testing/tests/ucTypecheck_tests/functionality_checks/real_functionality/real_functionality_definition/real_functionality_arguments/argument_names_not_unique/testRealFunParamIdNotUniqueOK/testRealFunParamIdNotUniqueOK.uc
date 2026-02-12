uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct D {
in x@bla()
}

direct A{D:D}

functionality R(F1:X1.A,F2:X2.A) implements A {

party P serves A.D { initial state I {match message with * => {fail.}end} }

}
