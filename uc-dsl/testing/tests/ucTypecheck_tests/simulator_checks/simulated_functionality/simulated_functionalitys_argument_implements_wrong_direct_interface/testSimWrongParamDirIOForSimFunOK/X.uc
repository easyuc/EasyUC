direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

direct D2' {
in  x@bla()
out bli()@x
}

direct D2 {D2:D2'}

adversarial Iio {
in  bla()
out bli()
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}
