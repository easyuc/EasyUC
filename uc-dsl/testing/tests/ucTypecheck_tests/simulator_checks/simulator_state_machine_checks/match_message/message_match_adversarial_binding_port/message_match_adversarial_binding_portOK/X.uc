direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio {
in  bla()
out bli()
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}
