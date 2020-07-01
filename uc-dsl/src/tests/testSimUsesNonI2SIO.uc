direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

functionality R() implements D {

 party P serves D {

  initial state I {
  match message with othermsg => {fail.} end
  }
 }
}

simulator S uses D simulates R() {

  initial state I {
  match message with D.othermsg => {fail.} end
  }

}
