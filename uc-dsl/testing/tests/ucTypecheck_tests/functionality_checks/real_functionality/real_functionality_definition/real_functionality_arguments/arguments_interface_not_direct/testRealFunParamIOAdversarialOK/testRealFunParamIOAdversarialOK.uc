direct D {
in x@bla()
}

direct A{D:D}

adversarial A_ {
in bla()
}

adversarial X{A:A_}

functionality R(F:A) implements A {

party P serves A.D { initial state I {match message with * => {fail.}end} }

}
