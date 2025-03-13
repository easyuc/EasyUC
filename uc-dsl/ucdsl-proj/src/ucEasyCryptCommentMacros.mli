(* UCEasyCryptCommentMacros module interface *)

(* EasyCrypt comment macros are defined as special EasyCrypt
   comments

   this module provides a function for returning the comment macros of
   an EasyCrypt file

   it also provides a function for applying a macro to arguments,
   yielding a string *)

(* exceptions raised by the function for scanning a file; the values
   of type int are line numbers, counting from 1, showing the location
   of an error message in a file *)

exception ECComMacs_NonterminatedComment of int  (* comment not closed *)
exception ECComMacs_UnmatchedClose       of int  (* extra comment close *)
exception ECComMacs_ScanError            of int  (* other scanning error *)

(* exception raised when checking a file, and also when applying
   a macro *)

exception ECComMacs_Error of string  (* post-scanning error *)

(* abstract type representing a list of macros

   each macro consists of a name (a string), parameters (a list of
   strings) and a body (a string)

   the name and parameters are sequences of letters digits, and underscores,
   beginning with a letter or underscore; the parameters must be distinct

   the body can have arbitrary whitespace in it, except not at its
   beginning or end

   there cannot be more than one macro with the same name in
   a list of macros *)

type macros

(* given a filename file, either fully qualified or interpreted
   relative to the current directory, scan_and_check_file file scans
   and checks the file, returning its list of macros, or raising an
   exception if there is an error

   - - -

   the file can include ordinary EasyCrypt-style nested comments,
   (* ... *)

   but *top-level* comments of the form (*! ... *) are required
   to define macros, where the ... starts with

     <name>(<par1>, ..., <parn>)

   possibly with whitespace characters inserted, and
   where <name> is the macro's name, and the <pari> are its
   parameters

   what follows in the ... is the <body> of the macro, except it is
   trimmed of initial and trailing whitespace; if it contains
   comments, they must be properly nested

   e.g.,

   (*! Bar(A, B) <<A>> : (*!<<B>>*) <<A>> A *)

   is a macro; see apply_macro below for the significance of the angle
   brackets

   the names of all the macros must be distinct *)

val scan_and_check_file : string -> macros

(* has_name macros name tests whether macros contains a macro with
   name name *)

val has_name : macros -> string -> bool

(* in a call apply_macro macs name args, if there is no macro in macs
   with name name, an ECComMacs_Error exception is raised; otherwise,
   suppose mac is the element of macs with name name

   if args has a different length than the list of parameters of mac,
   an ECComMacs_Error exception is raised

   otherwise, let (par1, arg1), ... (parn, argn) be
   the corresponding parameter/argument pairs

   the returned string is formed by starting with mac's body
   and working through the parameter/argument pairs in order:

     simultaneously substituting

       argi

     for all the (necessarily non-overlapping) substrings of the form

       "<<" ^ pari ^ ">>"

     and then continuing with the next substitution

     e.g., if the macro

       (*! Bar(A, B) <<A>> : (*!<<B>>*) <<A>> A *)

     is included in macs, then apply_macro macs "Bar" ["hi"; "bye"]
     will evaluate to

       hi : (*!bye*) hi A

     *note* that substitution inside a macro's body even happens
     inside comments; depending upon the arguments to a macro, the
     result of apply_macro may fail to have properly nested
     comments *)

val apply_macro : macros -> string -> string list -> string

(* begin for debugging *)

(* print a list of macros *)

val print_macros : macros -> unit

(* scan and check a file, printing out the resulting macros, and
   turning raised exceptions into error messages *)

val test_scan_and_check : string -> unit

(* test_subst file name [arg1; ...; argn], scans and checks
   file, yielding macs : macros, and then evaluates

     apply_macro macs name [arg1; ...; argn],

   printing out the resulting string, and turning raised exceptions
   into error messages *)

val test_subst : string -> string -> string list -> unit

(* end for debugging *)
