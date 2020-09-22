direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial iio {
in  bla()
out bli()
}

direct d2 {
in  x@bla2()
out bli2()@x
}

direct D2 {D2:d2}

adversarial a {
in  abla()
out abli()
}

adversarial A {A:a}

adversarial a2 {
in  abla2()
out abli2()
}

adversarial A2 {A2:a2}

functionality Q() implements D2 A2 {

 party P serves D2, A2 {

  initial state In {
  match message with othermsg => {fail.} end
  }
 }
}

functionality R(F:D) implements D A {

 subfun SFQ=Q()
 
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
  match message with R.F.D.D.bla() => {fail.} end
 }

}
