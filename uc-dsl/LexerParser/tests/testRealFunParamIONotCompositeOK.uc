direct D {
in x@bla()
}

direct A{d:D}

functionality R(F:A) implements A {

party P serves d { initial state I {match message with othermsg => {fail.}end} }

}
