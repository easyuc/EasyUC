direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

adversarial Iio {
in  bla()
out bli()
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}

simulator S uses Iio simulates I() {

  initial state In {
  match message with Iio.* => {fail.} end
  }

}
