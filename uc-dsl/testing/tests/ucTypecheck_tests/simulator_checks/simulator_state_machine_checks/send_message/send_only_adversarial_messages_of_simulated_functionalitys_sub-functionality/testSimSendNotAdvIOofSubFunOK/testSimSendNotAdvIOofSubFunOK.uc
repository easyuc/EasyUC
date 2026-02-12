uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

direct D2' {
in  x@bla2()
out bli2()@x
}

adversarial Iio {
in  i2sbla()
out i2sbli()
}

functionality R(F:X2.D) implements D {

 subfun SFQ=X1.Q
 
 party P serves D.D {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

simulator S uses Iio simulates R(X2.I) {

 initial state In {
  match message with Iio.i2sbli => { send R.SFQ.A2'.abli2() and transition Fin.} end
 }

 state Fin {
   match message with * => { fail. } end
 }
}
