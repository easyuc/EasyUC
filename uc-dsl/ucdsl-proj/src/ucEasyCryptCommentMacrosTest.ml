(* UcEasyCryptCommentMacrosTest module

   temporary module for testing EasyCrypt Comment Macros,
   using UcEasyCryptCommentMacros module *)

open UcEasyCryptCommentMacros

let () =
  match Array.to_list Sys.argv with
  | [_; file]                -> test_scan_and_check file
  | _ :: file :: mac :: args -> test_subst file mac args
  | _                        -> (Printf.eprintf "bad args\n"; exit 1)
