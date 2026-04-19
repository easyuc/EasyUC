(* UcProjectFiles module interface *)

(* "ucdsl.project" files allow the setting of the pretty printer
   margin, whether units checking is done, and what directories will
   be included in the search path

   ucdsl.project files can have bindings of the form

     units   = true
     units   = false
     margin  = <int>
     include = <directory>

   later bindings have precedence over earlier ones; later occurrences
   of units/margin overrule the previous ones; include directories are
   searched from later to earlier

   command line arguments have precedence over project bindings; in
   the case of include directories, the search path is first the
   includes from the command line arguments, and then the ones from
   the project file

   a project file is found by searcing from the directory of the UC DSL
   file being processed, or the current working directory if there
   is no such file, and working upwards

   relative include directories of the found project file are
   fully qualified by the directory of the project file *)

(* the result of processing the found ucdsl.project file *)

type project_params =
  {pp_includes : string list;  (* includes, from highest to lowest
                                  precedence *)
   pp_units    : bool option;  (* optionally, whether units checking
                                  should be done *)
   pp_margin   : int option}   (* optionally, the pretty printer margin *)

(* find and process the "ucdsl.project" file, returning the default result
   {pp_includes = []; pp_units = None; pp_margin = None}, if no
   such file is found

   if the argument is None, start searching in the current working
   directory

   if the argument is Some file, use the directory of file as the
   starting point, qualified by the current working directory when
   file is a relative path *)

val find_and_process_project_file : string option -> project_params
