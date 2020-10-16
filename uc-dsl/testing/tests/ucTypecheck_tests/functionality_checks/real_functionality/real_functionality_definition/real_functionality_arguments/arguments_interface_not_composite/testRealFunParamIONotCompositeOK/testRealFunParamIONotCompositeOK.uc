direct D {
in x@bla()
}

direct A{d:D}

functionality R(F:A) implements A {

party P serves A.d { initial state I {match message with *  => {fail.}end} }

}
