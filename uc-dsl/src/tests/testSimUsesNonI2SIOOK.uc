direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial iio {
in  bla()
out bli()
}

functionality R() implements D {

 party P serves D {

  initial state I {
  match message with othermsg => {fail.} end
  }
 }
}

simulator S uses iio simulates R() {

  initial state I {
  match message with iio.othermsg => {fail.} end
  }

}
