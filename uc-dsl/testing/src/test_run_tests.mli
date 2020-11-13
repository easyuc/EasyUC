val verbose : bool ref
val debug : bool ref
val quiet : bool ref

(* verbose, debug, quiet are flag which will be set to true
if corresponding option is used *)
  
val pre_verbose : string -> 'a

(* pre_verbose takes a directory as input and gets a list of all
TEST files in that directory using walk_directory_tree.
Then each file is parsed, checked for errors and then the unit test
will be 'run' after no errors found.

If all tests pass the routine exits with a code 0, if not the routine exits with code 1.
 *)
