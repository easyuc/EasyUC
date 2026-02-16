uc_requires X.
uc_clone X.

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

functionality R(F:X.D) implements D A {
 party P serves D.D A.A {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

simulator S uses Iio simulates R(X.I) {

 initial state In {
   match message with Iio.bli => {send Iio.bla and transition II.} end
 }

 state II() {
  match message with
  x@R.A.A.abla() => {fail.}
  | * => {fail.}
  end
 }

}
