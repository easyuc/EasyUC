direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio {
in  bla()
out bli()
}

direct D2' {
in  x@bla2()
out bli2()@x
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

adversarial A2 {A2:A2'}

functionality Q() implements D2 A2' {

  initial state In {
  match message with * => {fail.} end
  }
}

functionality R(F:D) implements D A {

 subfun SFQ=Q
 
 party P serves D.D A.A {
  initial state In {
  match message with * => {fail.} end
  }
 }
}

functionality I() implements D Iio {

  initial state In {
  match message with *  => {fail.} end
  }
}

simulator S uses Iio simulates R(I) {

 initial state In {
  match message with Iio.bli => {send Iio.bla and transition II.} end
 }

 state II() {
  match message with R.F.D.D.bla() => {fail.} end
 }

}
