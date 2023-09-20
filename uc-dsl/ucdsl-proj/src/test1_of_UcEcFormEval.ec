require import AllCore.
type dtty = [A of int | B of bool].

type foo = [
  | F of int & bool
  | T of (int * bool)
  | U
].
