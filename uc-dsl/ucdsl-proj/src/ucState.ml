(* UcState module *)

(* Global State of UC DSL tool *)

open Batteries

let include_dirs_ref : string list ref = ref []

let get_include_dirs () = ! include_dirs_ref

let set_include_dirs x = include_dirs_ref := x

let add_highest_include_dirs x =
  let dirs = List.remove (!include_dirs_ref) x in
  include_dirs_ref := x :: dirs

let add_lowest_include_dirs x =
  let dirs = List.remove (!include_dirs_ref) x in
  include_dirs_ref := dirs @ [x]

let raw_messages : bool ref = ref false

let set_raw_messages () = raw_messages := true

let get_raw_messages () = ! raw_messages

let units : bool ref = ref false

let set_units () = units := true

let get_units () = ! units
