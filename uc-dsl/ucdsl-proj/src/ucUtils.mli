(* UcUtils module interface *)

(* UC DSL Utilities *)

open Batteries
open EcLocation

(* try to find the first element in the list that also occurs later in
   the list, returning None if there is no such element, and Some of
   the element otherwise

   the default comparison function of list elements is
   Pervasives.compare *)

val find_dup : ?cmp:('a -> 'a -> int) -> 'a list -> 'a option

(* test whether the list has at least one duplicate element

   the default comparison function of list elements is
   Pervasives.compare *)

val has_dup  : ?cmp:('a -> 'a -> int) -> 'a list -> bool

(* return the index (counting from 0) of the first occurrence of an
   element in a list; raises Not_found if there is no such index

   Pervasives.compare is used for comparing list elements *)

val index_of_ex : 'a -> 'a list -> int

(* return the filename component of a located value *)

val filename_of_loc : EcLocation.t -> string

(* merge the locations of a list of located values, returning the
   dummy location when the list is empty *)

(* turn a filename into a Lexing.position that points to the beginning
   of the file *)

val begin_of_file_pos : string -> Lexing.position

(* turn a filename into a zero length range at the beginning
   of the file *)

val begin_of_file_loc : string -> EcLocation.t

val mergelocs : 'a located list -> EcLocation.t

(* label a value with the dummy location *)

val dummyloc : 'a -> 'a located

(* make an id path (list of strings) into a string using "." as
   a separator *)

val string_of_id_path : string list -> string

(* format (using an hv box) a list of strings using the given
   separator character *)

val format_strings : Format.formatter -> char -> string list -> unit

(* format a list of strings using "," as the separator character *)

val format_strings_comma : Format.formatter -> string list -> unit

(* apply string_of_id_path to each element of the list of id paths,
   and then use format_string_comma to format the resulting list of
   strings *)

val format_id_paths_comma : Format.formatter -> string list list -> unit

(* sl1_starts_with_sl2 sl1 sl2 tests whether sl2 is a prefix (possibly
   all of) sl1 *)

val sl1_starts_with_sl2 : string list -> string list -> bool

(* obtain the basename of a file (everything after the final "/", or
   everything if there is no "/"), remove the basename's
   extension (raises Invalid_argument if there is no extension), and
   then capitalize the first letter *)

val capitalized_root_of_filename_with_extension : string -> string

(* find_uc_root root prelude_dir include_dirs

   root should consist of a string of letters and digits whose initial
   character is capitalized; prelude_dir should be the fully qualified
   name of the UC DSL prelude directory; the elements of include_dirs
   should be fully qualified directories

   search for root in first the prelude_dir, or failing that, in the
   current directory, or failing that, in the directories of
   include_dirs (from front (highest precedence) to back (lowest
   precedence)); returns Some of the qualified filename (fully
   qualified, if not found in the current directory) if the search
   suceeds, or None if it fails

   when searching in a directory, we first look for the
   uncapitalization (just the first letter) of root concatenated with
   ".uc", and if that doesn't exist we look for root concatenated with
   ".uc"

   in a case-sensitive filesystem (e.g., Linux, normally), e.g., both
   foo.uc and Foo.uc could exist, in which case we find foo.uc

   in a case-insensitive / case-preserving filesystem (e.g., macOS,
   normally), only one of, e.g., foo.uc and Foo.uc can exist, and the
   returned qualified filename has the case that does exist *)

val find_uc_root : string -> string -> string list -> string option
  
