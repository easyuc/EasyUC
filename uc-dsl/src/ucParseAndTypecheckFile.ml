(* UcParseAndTypecheckFile module *)

(* parse and then typecheck a DSL specification *)

open EcLocation
open UcParseFile
open UcSpec
open UcTypedSpec
open UcTypecheck

(* for each run of parse_and_typecheck_file_or_id, we do:

   (+) checking that recursive uc_requires do not happen (the stack)

   (+) caching of results, to avoid recomputation (the cache) *)

type cache = typed_spec * UcEcScope.scope

let parse_and_typecheck_file_or_id foid =
  let stack : string list ref = ref [] in
  let cache : cache IdMap.t ref = ref IdMap.empty in
  let rec parse_and_typecheck foid =
    let (uc_root, loc_opt) =
      match foid with
      | FOID_File file ->
          (UcUtils.capitalized_root_of_filename_with_extension file, None)
      | FOID_Id id  -> (unloc id, Some(loc id)) in
    let () =
      if List.mem uc_root (!stack)
      then type_error (Option.get loc_opt)  (* will always be non-None *)
           (fun ppf ->
              Format.fprintf ppf
              "@[illegal@ recursion@ in@ UC@ requires:@;<1 2>%a@]"
              UcUtils.format_strings_comma (List.rev (uc_root :: !stack)))
      else stack := uc_root :: !stack in
    match IdMap.find_opt uc_root (!cache) with
    | None                      ->
        let (spec, qual_file) = parse_file_or_id foid in
        let tyspec =
          typecheck qual_file
          (fun id -> parse_and_typecheck (UcParseFile.FOID_Id id))
          spec in
        let () = stack := List.tl (!stack) in
        let cur_scope = UcEcCommands.ucdsl_current () in
        let () = cache := IdMap.add uc_root (tyspec, cur_scope) (!cache) in
        tyspec
    | Some (tyspec, saved_scope) ->
        let () = stack := List.tl (!stack) in
        let () = UcEcCommands.ucdsl_update saved_scope in
        tyspec
 in
  parse_and_typecheck foid
