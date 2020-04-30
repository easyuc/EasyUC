open DlParseFile
open DlUtils

let () = Printexc.record_backtrace true

let () = try ignore (parse_file Sys.argv.(1)) with exn -> printEx exn

