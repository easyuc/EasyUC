direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial Iio {
in  bla()
out bli()
}

functionality R(F:D) implements D {

 party P serves D.D {

  initial state In {
  match message with *  => {fail.} end
  }
 }
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}

simulator S uses Iio simulates R(I) {

 initial state In {
  match message with Iio.bli => {send Iio.bla and transition II.} end
 }

 state II() {
  match message with
  R.F.Iio.bla() => {fail.}
  | * => {fail.}
  end
 }

}
