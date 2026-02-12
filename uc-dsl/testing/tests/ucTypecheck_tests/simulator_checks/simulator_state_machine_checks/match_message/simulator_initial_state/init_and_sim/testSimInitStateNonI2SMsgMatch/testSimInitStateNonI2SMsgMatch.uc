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

functionality R(F:X.D) implements D {

 party P serves D.D {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

simulator S uses Iio simulates R(X.I) {

  initial state In {
  match message with R.D.D.* => {fail.} end
  }

}
