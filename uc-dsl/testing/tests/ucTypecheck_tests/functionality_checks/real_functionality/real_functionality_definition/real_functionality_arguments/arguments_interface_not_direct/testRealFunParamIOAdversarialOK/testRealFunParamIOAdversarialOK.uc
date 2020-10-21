direct D {
in x@bla()
}

direct A{d:D}

adversarial a {
in bla()
}

adversarial X{a:a}

functionality R(F:A) implements A {

party P serves A.d { initial state I {match message with * => {fail.}end} }

}
