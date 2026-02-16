direct D' {
in x@bla()
out bli()@x
}

adversarial Iio {
in  bla()
out bli()
}

direct D {D:D'}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}
