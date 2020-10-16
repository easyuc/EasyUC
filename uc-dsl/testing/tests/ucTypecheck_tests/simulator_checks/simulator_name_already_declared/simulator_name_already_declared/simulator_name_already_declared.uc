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

 party P serves D.D {

  initial state I {
  match message with * => {fail.} end
  }
 }
}

simulator R uses iio simulates R() {

  initial state I {
  match message with iio.* => {fail.} end
  }

}
