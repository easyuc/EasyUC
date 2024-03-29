(* test_types.ml *)

type outcome = Failure | Empty | Success

type expr =
  | Desc of string
  | Exec of string
  | Args of string list
  | Outcome of outcome * string
