direct D {
in x@bla()
}

direct A{D:D}

functionality R(A:A) implements A {

party P serves A.D { initial state I {match message with *  => {fail.}end} }

}
