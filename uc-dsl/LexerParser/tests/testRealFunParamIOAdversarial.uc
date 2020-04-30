direct D {
in x@bla()
}

direct A{d:D}

adversarial a {
in bla()
}

adversarial X{a:a}

functionality R(F:X) implements A {

party P serves d { initial state I {match message with othermsg => {fail.}end} }

}
