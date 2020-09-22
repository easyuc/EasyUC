direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial iio {
in  bla()
out bli()
}

adversarial a {
in  abla()
out abli()
}

adversarial A {A:a}

functionality R(F:D) implements D A {

 party P serves D, A {

  initial state In {
  match message with othermsg => {fail.} end
  }
 }
}

functionality I() implements D iio {

  initial state In {
  match message with othermsg => {fail.} end
  }
}

simulator S uses iio simulates R(I) {

 initial state In {
  match message with iio.othermsg => {fail.} end
 }

 state II() {
  match message with R.A.A.abla() => {fail.} end
 }

}
