uc_requires X.
uc_clone X.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial A' {
in  abla()
out abli()
}

adversarial A {A:A'}

adversarial Iio {
in  i2sbla()
out i2sbli()
}

functionality R(F:X.D) implements D A {

 party P serves D.D A.A {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

simulator S uses Iio simulates R(X.I) {

 initial state In {
  match message with Iio.* => {fail.} end
 }

}
