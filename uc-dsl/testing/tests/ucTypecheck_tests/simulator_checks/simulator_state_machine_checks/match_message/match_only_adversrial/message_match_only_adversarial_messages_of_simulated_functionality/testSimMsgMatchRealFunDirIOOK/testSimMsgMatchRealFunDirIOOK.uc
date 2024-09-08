direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio {
in  bla()
out bli()
}

adversarial A' {
in  abla()
out abli()
}

adversarial A {A:A'}

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
  match message with Iio.bli => {send Iio.bla and transition II.} end
 }

 state II() {
  match message with
  R.A.A.abla() => {fail.}
  | * => {fail.}
  end
 }

}
