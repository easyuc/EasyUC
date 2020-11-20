direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

adversarial Iio {
in  bla()
out bli()
}

adversarial A_ {
in  abla()
out abli()
}

adversarial A {A:A_}

functionality R(F:D) implements D A {

 party P serves D.D A.A {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}

simulator S uses Iio simulates R(I) {

 initial state In {
  match message with Iio.* => {fail.} end
 }

 state II() {
  match message with
  x@R.A.A.abla() => {fail.}
  | * => {fail.}
  end
 }

}
