uc_requires U.
uc_clone U.

direct D {
in x@bla()
}

direct A{D:D}

functionality R(F:U.X) implements A {

party P serves A.D { initial state I {match message with * => {fail.}end} }

}
