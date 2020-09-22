direct D {
in x@bla()
}

direct A{d:D}

functionality R(F:D) implements A {

party P serves d { initial state I {match message with othermsg => {fail.}end} }

}
