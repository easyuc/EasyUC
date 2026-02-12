direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio {
in  bla()
out bli()
}

functionality R() implements D {

 party P serves D.D {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

simulator S uses Iio simulates R() {

  initial state In {
  match message with Iio.* => {fail.} end
  }

}
