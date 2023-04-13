(* -------------------------------------------------------------------- *)

type ecreader
type ecreader_pty
type ecreader_pformula

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> ecreader
val from_file    : string -> ecreader
val from_string  : string -> ecreader

val from_channel_pty : name:string -> in_channel -> ecreader_pty
val from_file_pty    : string -> ecreader_pty
val from_string_pty  : string -> ecreader_pty

val from_channel_pformula : name:string -> in_channel -> ecreader_pformula
val from_file_pformula    : string -> ecreader_pformula
val from_string_pformula  : string -> ecreader_pformula

(* -------------------------------------------------------------------- *)
val finalize : ecreader -> unit
val parse    : ecreader -> EcParsetree.prog

val finalize_pty : ecreader_pty -> unit
val parse_pty    : ecreader_pty -> EcParsetree.pty

val finalize_pformula : ecreader_pformula -> unit
val parse_pformula    : ecreader_pformula -> EcParsetree.pformula

val parseall : ecreader -> EcParsetree.global list
val drain    : ecreader -> unit
val lexbuf   : ecreader -> Lexing.lexbuf

(* -------------------------------------------------------------------- *)
val lex_single_token : string -> EcParser.token option
val is_sym_ident : string -> bool
val is_op_ident  : string -> bool
val is_mem_ident : string -> bool
val is_mod_ident : string -> bool

(* -------------------------------------------------------------------- *)
val is_binop     : string -> [`Yes | `No | `Invalid]
val is_uniop     : string -> [`Yes | `No | `Invalid]
