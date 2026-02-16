uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

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

functionality R(F:X2.D) implements D A {

 subfun SFQ=X1.Q
 
 party P serves D.D A.A {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

simulator S uses Iio simulates R(X2.I) {

 initial state In {
  match message with Iio.bli => {send Iio.bla and transition II.} end
 }

 state II() {
  match message with
  R.SFQ.A2'.abla2() => {fail.}
  | * => {fail.}
  end
 }
}
