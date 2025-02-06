ec_requires +Main.

direct D' {
  in pt@req(x : t)
}

direct D {
  D' : D'
}

functionality Main implements D {
  initial state Init {
    match message with
    | pt@D.D'.req(x) => {
        if (f x = 0) {
          fail.
        }
        else {
          fail.
        }
      }
    end
  }
}

