direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio2 {
in  i2sbla()
out i2sbli()
}

functionality I() implements D Iio2 {

  initial state In {
  match message with * => {fail.} end
  }
}
