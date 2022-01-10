(* test_common_module *)
(* This file contains functions which are used by various
other files *)

open Test_types
   
exception Error of string

val print_list : expr list -> unit

(* print_list takes a list of expressions as in input and prints 
each of the expressions in the list. Here expressions are of type
Desc of string or Args of string list or Outcome of outcome * string 

One way to get expr list is to use the function parse which takes
a file as input and generates expr list
*)

val check_ec_standard : string -> string

(* check_ec_standard takes a file_name as input and checks whether
the file_name matches EasyCrypt file naming conventions. If the
file_name doesn't match EasyCrypt convention, a warning message
will be returned *)
  
val check_fields : expr list -> string * string
(* check_fileds takes an expression list and checks whether there
are any multiple args/outcomes given or args/outcomes is missing and 
returns error in either case which corresponds to the first string
in the return type string * string

It also checks for multiple or missing
description, in this case a warning is returned - which corresponds to
the second string in string * string.

The return type string * string can be read as errors * warning
If no error or warning is found, empty string will be returned
for that part
*)
  
val get_desc : expr list -> string

(*like the name suggests, get_desc takes expr list and
return description as a string *)
                               
val read_file : string -> string

  (* Like the name suggests, read_file takes a file_name
and converts contents of that file into a string
   *)
  
val parse : string -> expr list

  (* parse takes a TEST file and converts it into
a list of expressions
   *)
  
val walk_directory_tree :
  string -> string list -> string -> string list * string

  (* walk_directory_tree takes a directory and searches for
TEST files in that directory and all subdirectories

(* The acceptable content of a director are
	| TEST file + contents + optional sub directories
	| If a TEST file is found, subfolders will be ignored
	| Files with names starting with "readme" only + 
                                    optional sub directories
                (readme is case insenstive)
	| Only sub folders will be searched for TEST files/tests
	| No files but sub directories
	| All subdirectories will be searched for TEST files/tests
	| Any others will be ignored
        | log file
	
 *)

   *)
  
val run : string -> string array -> int option * string

(* run takes a folder, string array and returns std out and exit code

string array contains options and a command as the last entry in this 
list. This folder is used to go to that folder and run the command
with all given options

 *)
