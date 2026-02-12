direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

direct D2' {
in  x@bla2()
out bli2()@x
}

adversarial Iio {
in  i2sbla()
out i2sbli()
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}
