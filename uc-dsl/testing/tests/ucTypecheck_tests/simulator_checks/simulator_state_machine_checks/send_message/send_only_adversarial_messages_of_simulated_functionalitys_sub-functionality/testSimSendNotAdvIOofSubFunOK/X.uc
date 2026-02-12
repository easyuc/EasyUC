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

direct D2 {D2:D2'}

adversarial A' {
in  abla()
out abli()
}

adversarial A {A:A'}

adversarial A2' {
in  abla2()
out abli2()
}

functionality Q() implements D2 A2' {

  initial state In {
  match message with * => {fail.} end
  }
}
