direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial iio {
in  bla()
out bli()
}

functionality R(F:D) implements D {

 party P serves D.D {
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

simulator S uses iio simulates R(R) {

  initial state In {
  match message with iio.* => {fail.} end
  }

}