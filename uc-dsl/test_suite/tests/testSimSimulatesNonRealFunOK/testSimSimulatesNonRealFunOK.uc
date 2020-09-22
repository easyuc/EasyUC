direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial iio {
in  bla()
out bli()
}

functionality I() implements D {
 party P serves D {
  initial state In {
  match message with othermsg => {fail.} end
  }
 }
}

simulator S uses iio simulates I() {

  initial state In {
  match message with iio.othermsg => {fail.} end
  }

}
