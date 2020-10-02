direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

direct d2 {
in  x@bla2()
out bli2()@x
}

direct D2 {D2:d2}

adversarial a {
in  abla()
out abli()
}

adversarial A {A:a}

adversarial a2 {
in  abla2()
out abli2()
}

adversarial A2 {A2:a2}

adversarial iio {
in  i2sbla()
out i2sbli()
}

functionality Q() implements D2 a2 {

  initial state In {
  match message with * => {fail.} end
  }
}

functionality R(F:D) implements D A {

 subfun SFQ=Q

 party P serves D.D A.A {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

functionality I() implements D iio {

  initial state In {
  match message with * => {fail.} end
  }
}

simulator S uses iio simulates R(I) {

 initial state In {
 match message with iio.othermsg => { send R.SFQ.A2.A2.abli2() and transition In.} end
 }

}
