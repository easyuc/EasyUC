uc_requires X.
uc_clone X.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio {
in  i2sbla()
out i2sbli()
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
  match message with Iio.i2sbli => { send R.F.Iio.i2sbli() and transition In.} end
 }

 state Fin {
   match message with * => { fail. } end
 }
}
