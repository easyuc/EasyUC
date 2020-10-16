direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial a {
in  abla()
out abli()
}

adversarial A {A:a}

adversarial iio {
in  i2sbla()
out i2sbli()
}

functionality R(F:D) implements D A {

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
  match message with iio.* => {fail.} end
 }

}
