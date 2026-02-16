uc_requires X.
uc_clone X.

direct D {
in x@bla()
}

direct A{D:D}

functionality R(F:X.A) implements A {

party P serves A.D { initial state I {match message with *  => {fail.}end} }

}
