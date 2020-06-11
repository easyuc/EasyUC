
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | WITH
    | VAR
    | USES
    | UNDERSCORE
    | TRANSITION
    | SUBFUN
    | STATE
    | STAR
    | SIMS
    | SIM
    | SERVES
    | SEND
    | SEMICOLON
    | RPAREN
    | ROP4 of (
# 86 "dlParser.mly"
       (string)
# 25 "dlParser.ml"
  )
    | REQUIRES
    | RBRACE
    | PIPE
    | PARTY
    | OUT
    | OTHERMSG
    | OR
    | OK
    | NOT
    | MESSAGE
    | MATCH
    | LPAREN
    | LBRACE
    | INITIAL
    | IN
    | IMPORT
    | IMPLEM
    | IF
    | ID of (
# 26 "dlParser.mly"
       (string)
# 48 "dlParser.ml"
  )
    | HAT
    | FUNCT
    | FAIL
    | ERROR
    | EQ
    | EOF
    | END
    | ENCODE
    | ELSE
    | ELIF
    | DOT
    | DIRIO
    | DECODE
    | COMMA
    | COLON
    | AT
    | ASGVAL
    | ASGSAMPLE
    | AS
    | ARROW
    | ANDTXT
    | AND
    | ADVIO
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState345
  | MenhirState341
  | MenhirState329
  | MenhirState326
  | MenhirState319
  | MenhirState311
  | MenhirState309
  | MenhirState301
  | MenhirState292
  | MenhirState289
  | MenhirState285
  | MenhirState284
  | MenhirState283
  | MenhirState279
  | MenhirState265
  | MenhirState260
  | MenhirState258
  | MenhirState255
  | MenhirState254
  | MenhirState250
  | MenhirState248
  | MenhirState239
  | MenhirState236
  | MenhirState233
  | MenhirState230
  | MenhirState229
  | MenhirState227
  | MenhirState223
  | MenhirState222
  | MenhirState220
  | MenhirState216
  | MenhirState212
  | MenhirState211
  | MenhirState209
  | MenhirState206
  | MenhirState199
  | MenhirState197
  | MenhirState192
  | MenhirState187
  | MenhirState181
  | MenhirState172
  | MenhirState165
  | MenhirState161
  | MenhirState157
  | MenhirState152
  | MenhirState150
  | MenhirState145
  | MenhirState142
  | MenhirState137
  | MenhirState136
  | MenhirState134
  | MenhirState131
  | MenhirState130
  | MenhirState129
  | MenhirState127
  | MenhirState122
  | MenhirState109
  | MenhirState107
  | MenhirState105
  | MenhirState103
  | MenhirState101
  | MenhirState99
  | MenhirState92
  | MenhirState89
  | MenhirState86
  | MenhirState85
  | MenhirState84
  | MenhirState83
  | MenhirState82
  | MenhirState81
  | MenhirState79
  | MenhirState78
  | MenhirState77
  | MenhirState70
  | MenhirState64
  | MenhirState63
  | MenhirState61
  | MenhirState55
  | MenhirState49
  | MenhirState47
  | MenhirState46
  | MenhirState45
  | MenhirState40
  | MenhirState34
  | MenhirState32
  | MenhirState29
  | MenhirState28
  | MenhirState26
  | MenhirState23
  | MenhirState17
  | MenhirState15
  | MenhirState14
  | MenhirState8
  | MenhirState2
  | MenhirState1

# 3 "dlParser.mly"
  

open EcUtils
open EcLocation
open DlParseTree

let toId (mtid:msgType) =
	match mtid with
	| MsgType id -> id
	| OtherMsg l -> parse_error l (Some "othermsg keyword cannot be followed by '.' ")

let rec r_mtl2msgPath (mtl:msgType list) (mp:msgPath)=
	match mtl with
	| [] -> raise (Failure "Cannot happen: empty list when converting mtl to msgPath")
	| [x] -> {ioPath = mp.ioPath;msgType = x}
	| hd::tl -> r_mtl2msgPath tl {ioPath = mp.ioPath @ [toId hd]; msgType = mp.msgType}

let mtl2msgPath (mtl:msgType list) = r_mtl2msgPath mtl {ioPath=[];msgType=OtherMsg _dummy}



# 207 "dlParser.ml"

let rec _menhir_goto_assignment : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.instruction) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (DlParseTree.instruction)) = _v in
    let _startpos_i_ = _startpos in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (DlParseTree.instruction) = 
# 585 "dlParser.mly"
                ( i )
# 221 "dlParser.ml"
     in
    _menhir_goto_instruction_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_separated_nonempty_list_COMMA_expression_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.expressionL list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState122 | MenhirState81 | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.expressionL list)) = _v in
        let _v : (DlParseTree.expressionL list) = 
# 144 "<standard.mly>"
    ( x )
# 235 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.expressionL list)) = _v in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.expressionL list) = let x =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 255 "dlParser.ml"
            
          in
          
# 740 "dlParser.mly"
                                         ( x )
# 261 "dlParser.ml"
          
        in
        
# 243 "<standard.mly>"
    ( x :: xs )
# 267 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_expression_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run99 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (DlParseTree.expression) * Lexing.position -> Lexing.position -> (
# 86 "dlParser.mly"
       (string)
# 276 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState99 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState99 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99

and _menhir_run101 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (DlParseTree.expression) * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101

and _menhir_run103 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (DlParseTree.expression) * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState103 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState103

and _menhir_run105 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (DlParseTree.expression) * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105

and _menhir_run107 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (DlParseTree.expression) * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107

and _menhir_goto_separated_nonempty_list_PIPE_msgMatchCode_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgMatchCode list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.msgMatchCode list)) = _v in
        let _v : (DlParseTree.msgMatchCode list) = 
# 144 "<standard.mly>"
    ( x )
# 382 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_PIPE_msgMatchCode__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState236 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.msgMatchCode list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.msgMatchCode))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.msgMatchCode list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 394 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_PIPE_msgMatchCode_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_PIPE_msgMatchCodeSim_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgMatchCode list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.msgMatchCode list)) = _v in
        let _v : (DlParseTree.msgMatchCode list) = 
# 144 "<standard.mly>"
    ( x )
# 410 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_PIPE_msgMatchCodeSim__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.msgMatchCode list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.msgMatchCode))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.msgMatchCode list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 422 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_PIPE_msgMatchCodeSim_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_iftail : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.instructionL list option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_ift_ = _endpos in
        let (ift : (DlParseTree.instructionL list option)) = _v in
        let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x_, _, (x : (DlParseTree.expression)), _startpos_x_), _endpos__4_), _endpos_tins_, _, (tins : (DlParseTree.instructionL list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_ift_ in
        let _v : (DlParseTree.instruction) = let c =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 453 "dlParser.ml"
            
          in
          
# 740 "dlParser.mly"
                                         ( x )
# 459 "dlParser.ml"
          
        in
        
# 611 "dlParser.mly"
                                                                 ( ITE (c,tins,ift) )
# 465 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_x_ = _endpos in
        let (x : (DlParseTree.instruction)) = _v in
        let _startpos_x_ = _startpos in
        let _endpos = _endpos_x_ in
        let _v : (DlParseTree.instructionL list option) = let elif =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 484 "dlParser.ml"
            
          in
          
# 609 "dlParser.mly"
                                             ( x )
# 490 "dlParser.ml"
          
        in
        
# 607 "dlParser.mly"
                        ( Some [elif])
# 496 "dlParser.ml"
         in
        _menhir_goto_iftail _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_ift_ = _endpos in
        let (ift : (DlParseTree.instructionL list option)) = _v in
        let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x_, _, (x : (DlParseTree.expression)), _startpos_x_), _endpos__4_), _endpos_tins_, _, (tins : (DlParseTree.instructionL list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_ift_ in
        let _v : (DlParseTree.instruction) = let c =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 521 "dlParser.ml"
            
          in
          
# 740 "dlParser.mly"
                                         ( x )
# 527 "dlParser.ml"
          
        in
        
# 602 "dlParser.mly"
                                                                ( ITE (c,tins,ift) )
# 533 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_i_ = _endpos in
        let (i : (DlParseTree.instruction)) = _v in
        let _startpos_i_ = _startpos in
        let _startpos = _startpos_i_ in
        let _endpos = _endpos_i_ in
        let _v : (DlParseTree.instruction) = 
# 586 "dlParser.mly"
                ( i )
# 545 "dlParser.ml"
         in
        _menhir_goto_instruction_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _endpos) = Obj.magic _menhir_stack in
    let _v : (DlParseTree.instructionL list option) = 
# 605 "dlParser.mly"
                 ( None       )
# 557 "dlParser.ml"
     in
    _menhir_goto_iftail _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run131 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131

and _menhir_run133 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ENCODE ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState134 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState134 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAREN ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState134 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState134 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState134)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_stateInstance : _menhir_env -> 'ttv_tail -> (DlParseTree.stateInstance) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (state : (DlParseTree.stateInstance)) = _v in
    let ((_menhir_stack, _menhir_s, _startpos__1_), _, (msg : (DlParseTree.msgInstance))) = _menhir_stack in
    let _4 = () in
    let _3 = () in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _v : (DlParseTree.sendAndTransition) = 
# 710 "dlParser.mly"
                                                                    ( {msg=msg; state=state} )
# 619 "dlParser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__2_ = _endpos in
        let (_menhir_stack, _menhir_s, (sat : (DlParseTree.sendAndTransition)), _startpos_sat_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_sat_ in
        let _endpos = _endpos__2_ in
        let _v : (DlParseTree.instruction) = 
# 664 "dlParser.mly"
                               ( SendAndTransition sat )
# 639 "dlParser.ml"
         in
        _menhir_goto_terminal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_option_dest_ : _menhir_env -> 'ttv_tail -> (DlParseTree.id option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (portVar : (DlParseTree.id option)) = _v in
    let ((((_menhir_stack, _menhir_s, (path : (DlParseTree.msgPath))), _startpos__2_), _, (xs : (DlParseTree.expressionL list))), _endpos__4_) = _menhir_stack in
    let _4 = () in
    let _2 = () in
    let _v : (DlParseTree.msgInstance) = let tupleInstance = 
# 232 "<standard.mly>"
    ( xs )
# 660 "dlParser.ml"
     in
    
# 713 "dlParser.mly"
                                                                                                       ( {path=path; tupleInstance=tupleInstance; portVar=portVar} )
# 665 "dlParser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANDTXT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TRANSITION ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ENCODE ->
                        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | ID _v ->
                        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LPAREN ->
                        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | NOT ->
                        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | RPAREN ->
                        _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack) MenhirState122
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122)
                | DOT ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 716 "dlParser.ml"
                    )), _startpos_x_) = _menhir_stack in
                    let _v : (DlParseTree.stateInstance) = let id =
                      let idL =
                        let _endpos = _endpos_x_ in
                        let _startpos = _startpos_x_ in
                        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 729 "dlParser.ml"
                        
                      in
                      
# 129 "dlParser.mly"
              ( idL )
# 735 "dlParser.ml"
                      
                    in
                    
# 719 "dlParser.mly"
           ( {id=id; params=None} )
# 741 "dlParser.ml"
                     in
                    _menhir_goto_stateInstance _menhir_env _menhir_stack _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_expression_u : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.expression) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_x_, _, (x : (DlParseTree.expression)), _startpos_x_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_ in
        let _v : (DlParseTree.expression) = let e =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 790 "dlParser.ml"
            
          in
          
# 740 "dlParser.mly"
                                         ( x )
# 796 "dlParser.ml"
          
        in
        
# 746 "dlParser.mly"
                                                     ( Enc e            )
# 802 "dlParser.ml"
         in
        _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState122 | MenhirState81 | MenhirState109 | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ENCODE ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ID _v ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAREN ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109)
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_) = _menhir_stack in
            let _v : (DlParseTree.expressionL list) = let x =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 851 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 857 "dlParser.ml"
              
            in
            
# 241 "<standard.mly>"
    ( [ x ] )
# 863 "dlParser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_expression_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AS | COMMA | EQ | HAT | OR | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_), _endpos_x_inlined1_, (x_inlined1 : (
# 86 "dlParser.mly"
       (string)
# 884 "dlParser.ml"
            )), _startpos_x_inlined1_), _endpos_x_inlined2_, _, (x_inlined2 : (DlParseTree.expression)), _startpos_x_inlined2_) = _menhir_stack in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_inlined2_ in
            let _v : (DlParseTree.expression) = let e2 =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined2_, _startpos_x_inlined2_, x_inlined2) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 900 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 906 "dlParser.ml"
              
            in
            let op =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let op = 
# 735 "dlParser.mly"
        (  x    )
# 915 "dlParser.ml"
                 in
                
# 738 "dlParser.mly"
            ( op    )
# 920 "dlParser.ml"
                
              in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 932 "dlParser.ml"
              
            in
            let e1 =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 946 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 952 "dlParser.ml"
              
            in
            
# 744 "dlParser.mly"
                                                     ( App (op,[e1;e2]) )
# 958 "dlParser.ml"
             in
            _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AS | COMMA | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_), _endpos__1_, _startpos__1_), _endpos_x_inlined1_, _, (x_inlined1 : (DlParseTree.expression)), _startpos_x_inlined1_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_inlined1_ in
            let _v : (DlParseTree.expression) = let e2 =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1000 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1006 "dlParser.ml"
              
            in
            let op =
              let x =
                let op = 
# 732 "dlParser.mly"
        ( "\\/" )
# 1014 "dlParser.ml"
                 in
                
# 738 "dlParser.mly"
            ( op    )
# 1019 "dlParser.ml"
                
              in
              let (_endpos_x_, _startpos_x_) = (_endpos__1_, _startpos__1_) in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1032 "dlParser.ml"
              
            in
            let e1 =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1046 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1052 "dlParser.ml"
              
            in
            
# 744 "dlParser.mly"
                                                     ( App (op,[e1;e2]) )
# 1058 "dlParser.ml"
             in
            _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState103 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AS | COMMA | EQ | HAT | OR | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_), _endpos__1_, _startpos__1_), _endpos_x_inlined1_, _, (x_inlined1 : (DlParseTree.expression)), _startpos_x_inlined1_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_inlined1_ in
            let _v : (DlParseTree.expression) = let e2 =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1092 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1098 "dlParser.ml"
              
            in
            let op =
              let x =
                let op = 
# 734 "dlParser.mly"
        ( "^"   )
# 1106 "dlParser.ml"
                 in
                
# 738 "dlParser.mly"
            ( op    )
# 1111 "dlParser.ml"
                
              in
              let (_endpos_x_, _startpos_x_) = (_endpos__1_, _startpos__1_) in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1124 "dlParser.ml"
              
            in
            let e1 =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1138 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1144 "dlParser.ml"
              
            in
            
# 744 "dlParser.mly"
                                                     ( App (op,[e1;e2]) )
# 1150 "dlParser.ml"
             in
            _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AS | COMMA | OR | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_), _endpos__1_, _startpos__1_), _endpos_x_inlined1_, _, (x_inlined1 : (DlParseTree.expression)), _startpos_x_inlined1_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_inlined1_ in
            let _v : (DlParseTree.expression) = let e2 =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1186 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1192 "dlParser.ml"
              
            in
            let op =
              let x =
                let op = 
# 731 "dlParser.mly"
        ( "="   )
# 1200 "dlParser.ml"
                 in
                
# 738 "dlParser.mly"
            ( op    )
# 1205 "dlParser.ml"
                
              in
              let (_endpos_x_, _startpos_x_) = (_endpos__1_, _startpos__1_) in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1218 "dlParser.ml"
              
            in
            let e1 =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1232 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1238 "dlParser.ml"
              
            in
            
# 744 "dlParser.mly"
                                                     ( App (op,[e1;e2]) )
# 1244 "dlParser.ml"
             in
            _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AS | COMMA | OR | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_), _endpos__1_, _startpos__1_), _endpos_x_inlined1_, _, (x_inlined1 : (DlParseTree.expression)), _startpos_x_inlined1_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_inlined1_ in
            let _v : (DlParseTree.expression) = let e2 =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1284 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1290 "dlParser.ml"
              
            in
            let op =
              let x =
                let op = 
# 733 "dlParser.mly"
        ( "/\\" )
# 1298 "dlParser.ml"
                 in
                
# 738 "dlParser.mly"
            ( op    )
# 1303 "dlParser.ml"
                
              in
              let (_endpos_x_, _startpos_x_) = (_endpos__1_, _startpos__1_) in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1316 "dlParser.ml"
              
            in
            let e1 =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1330 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1336 "dlParser.ml"
              
            in
            
# 744 "dlParser.mly"
                                                     ( App (op,[e1;e2]) )
# 1342 "dlParser.ml"
             in
            _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AS | COMMA | OR | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _endpos_x_, _, (x : (DlParseTree.expression)), _startpos_x_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_x_ in
            let _v : (DlParseTree.expression) = let e =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1379 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1385 "dlParser.ml"
              
            in
            let op =
              let x = 
# 728 "dlParser.mly"
         ( "[!]" )
# 1392 "dlParser.ml"
               in
              let (_endpos_x_, _startpos_x_) = (_endpos__1_, _startpos__1_) in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1404 "dlParser.ml"
              
            in
            
# 745 "dlParser.mly"
                                                     ( App (op,[e])     )
# 1410 "dlParser.ml"
             in
            _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 1511 "dlParser.ml"
            )), _startpos_x_), _endpos_x_inlined1_, _, (x_inlined1 : (DlParseTree.expression)), _startpos_x_inlined1_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos__4_ in
            let _v : (DlParseTree.instruction) = let e =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1529 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1535 "dlParser.ml"
              
            in
            let vid =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1549 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 1555 "dlParser.ml"
              
            in
            
# 650 "dlParser.mly"
                                               ( Assign (vid,e) )
# 1561 "dlParser.ml"
             in
            _menhir_goto_assignment _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState145 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 1594 "dlParser.ml"
            )), _startpos_x_), _endpos_x_inlined1_, _, (x_inlined1 : (DlParseTree.expression)), _startpos_x_inlined1_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos__4_ in
            let _v : (DlParseTree.instruction) = let e =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1612 "dlParser.ml"
                
              in
              
# 740 "dlParser.mly"
                                         ( x )
# 1618 "dlParser.ml"
              
            in
            let vid =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1632 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 1638 "dlParser.ml"
              
            in
            
# 651 "dlParser.mly"
                                               ( Sample (vid,e) )
# 1644 "dlParser.ml"
             in
            _menhir_goto_assignment _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAREN ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152)
        | EQ ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HAT ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OR ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ROP4 _v ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_s_expression_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.expressionL list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_xs_ = _endpos in
        let (xs : (DlParseTree.expressionL list)) = _v in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (DlParseTree.expressionL list) = let x =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1711 "dlParser.ml"
            
          in
          
# 775 "dlParser.mly"
                                             ( x )
# 1717 "dlParser.ml"
          
        in
        
# 223 "<standard.mly>"
    ( x :: xs )
# 1723 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_s_expression_ _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_args_ = _endpos in
        let (args : (DlParseTree.expressionL list)) = _v in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 1734 "dlParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_args_ in
        let _v : (DlParseTree.expression) = let f =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1749 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 1755 "dlParser.ml"
          
        in
        
# 743 "dlParser.mly"
                                                     ( App (f,args)     )
# 1761 "dlParser.ml"
         in
        _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_instruction_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.instructionL list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (insts : (DlParseTree.instructionL list)) = _v in
        let _v : (DlParseTree.instructionL list) = 
# 581 "dlParser.mly"
                                         ( insts )
# 1777 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s), _, (is : (DlParseTree.instructionL list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _endpos = _endpos__3_ in
            let _v : (DlParseTree.instructionL list) = 
# 591 "dlParser.mly"
                                 ( is  )
# 1797 "dlParser.ml"
             in
            let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState129 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ELIF ->
                    _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | ELSE ->
                    _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState130
                | DECODE | FAIL | ID _ | IF | RBRACE | SEND ->
                    _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState130
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130)
            | MenhirState131 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _endpos_eins_, _, (eins : (DlParseTree.instructionL list))) = _menhir_stack in
                let _1 = () in
                let _endpos = _endpos_eins_ in
                let _v : (DlParseTree.instructionL list option) = 
# 606 "dlParser.mly"
                         ( Some eins  )
# 1825 "dlParser.ml"
                 in
                _menhir_goto_iftail _menhir_env _menhir_stack _endpos _menhir_s _v
            | MenhirState136 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ELIF ->
                    _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | ELSE ->
                    _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState137
                | DECODE | FAIL | ID _ | IF | RBRACE | SEND ->
                    _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState137
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137)
            | MenhirState161 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | PIPE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ERROR ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | ARROW ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | LBRACE ->
                                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState165
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState165 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | END ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos__15_ = _endpos in
                    let (((((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_x_, _, (x : (DlParseTree.expression)), _startpos_x_), _, (ty : (DlParseTree.ty))), (_6 : (unit option))), _, (tM : (DlParseTree.matchItem list))), _endpos_code1_, _, (code1 : (DlParseTree.instructionL list))), _endpos_code2_, _, (code2 : (DlParseTree.instructionL list))) = _menhir_stack in
                    let _15 = () in
                    let _13 = () in
                    let _12 = () in
                    let _11 = () in
                    let _9 = () in
                    let _7 = () in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _startpos = _startpos__1_ in
                    let _endpos = _endpos__15_ in
                    let _v : (DlParseTree.instruction) = let ex =
                      let x =
                        let _endpos = _endpos_x_ in
                        let _startpos = _startpos_x_ in
                        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 1921 "dlParser.ml"
                        
                      in
                      
# 740 "dlParser.mly"
                                         ( x )
# 1927 "dlParser.ml"
                      
                    in
                    
# 623 "dlParser.mly"
 ( Decode (ex,ty,tM,code1,code2) )
# 1933 "dlParser.ml"
                     in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos_i_ = _endpos in
                    let (i : (DlParseTree.instruction)) = _v in
                    let _startpos_i_ = _startpos in
                    let _startpos = _startpos_i_ in
                    let _endpos = _endpos_i_ in
                    let _v : (DlParseTree.instruction) = 
# 587 "dlParser.mly"
                ( i )
# 1945 "dlParser.ml"
                     in
                    _menhir_goto_instruction_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState77 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (patternMatch : (DlParseTree.msgMatch))), _endpos_code_, _, (code : (DlParseTree.instructionL list))) = _menhir_stack in
                let _2 = () in
                let _v : (DlParseTree.msgMatchCode) = 
# 571 "dlParser.mly"
                                                    ( {patternMatch=patternMatch; code=code } )
# 1962 "dlParser.ml"
                 in
                let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | PIPE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ID _v ->
                        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | OTHERMSG ->
                        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState181)
                | END ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (x : (DlParseTree.msgMatchCode))) = _menhir_stack in
                    let _v : (DlParseTree.msgMatchCode list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 1988 "dlParser.ml"
                     in
                    _menhir_goto_separated_nonempty_list_PIPE_msgMatchCodeSim_ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState239 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (patternMatch : (DlParseTree.msgMatch))), _endpos_code_, _, (code : (DlParseTree.instructionL list))) = _menhir_stack in
                let _2 = () in
                let _v : (DlParseTree.msgMatchCode) = 
# 490 "dlParser.mly"
                                                 ( {patternMatch=patternMatch; code=code } )
# 2005 "dlParser.ml"
                 in
                let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | PIPE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ID _v ->
                        _menhir_run228 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | OTHERMSG ->
                        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState236)
                | END ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (x : (DlParseTree.msgMatchCode))) = _menhir_stack in
                    let _v : (DlParseTree.msgMatchCode list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 2031 "dlParser.ml"
                     in
                    _menhir_goto_separated_nonempty_list_PIPE_msgMatchCode_ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.instructionL list)) = _v in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.instruction)), _startpos_x_) = _menhir_stack in
        let _v : (DlParseTree.instructionL list) = let x =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2064 "dlParser.ml"
            
          in
          
# 583 "dlParser.mly"
                                            ( x )
# 2070 "dlParser.ml"
          
        in
        
# 223 "<standard.mly>"
    ( x :: xs )
# 2076 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_instruction_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.expressionL list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (xs : (DlParseTree.expressionL list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (DlParseTree.expression) = let es = 
# 232 "<standard.mly>"
    ( xs )
# 2105 "dlParser.ml"
             in
            
# 778 "dlParser.mly"
                                                        ( Tuple es )
# 2110 "dlParser.ml"
             in
            _menhir_goto_s_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos_x_ = _endpos in
                    let (x : (
# 26 "dlParser.mly"
       (string)
# 2146 "dlParser.ml"
                    )) = _v in
                    let _startpos_x_ = _startpos in
                    let _1 = () in
                    let _v : (DlParseTree.id) = let pv =
                      let idL =
                        let _endpos = _endpos_x_ in
                        let _startpos = _startpos_x_ in
                        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2161 "dlParser.ml"
                        
                      in
                      
# 129 "dlParser.mly"
              ( idL )
# 2167 "dlParser.ml"
                      
                    in
                    
# 715 "dlParser.mly"
                   ( pv )
# 2173 "dlParser.ml"
                     in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (x : (DlParseTree.id)) = _v in
                    let _v : (DlParseTree.id option) = 
# 116 "<standard.mly>"
    ( Some x )
# 2181 "dlParser.ml"
                     in
                    _menhir_goto_option_dest_ _menhir_env _menhir_stack _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | ANDTXT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _v : (DlParseTree.id option) = 
# 114 "<standard.mly>"
    ( None )
# 2194 "dlParser.ml"
                 in
                _menhir_goto_option_dest_ _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 2223 "dlParser.ml"
            )), _startpos_x_), _startpos__2_), _, (xs : (DlParseTree.expressionL list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (DlParseTree.stateInstance) = let params = 
# 232 "<standard.mly>"
    ( xs )
# 2230 "dlParser.ml"
             in
            let id =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2243 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 2249 "dlParser.ml"
              
            in
            
# 718 "dlParser.mly"
                                                                    ( {id=id; params=Some params} )
# 2255 "dlParser.ml"
             in
            _menhir_goto_stateInstance _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_qid_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.qid list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState250 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.qid list)) = _v in
        let (_menhir_stack, _endpos_qid_, _menhir_s, (qid : (DlParseTree.qid)), _startpos_qid_) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.qid list) = let x = 
# 132 "dlParser.mly"
                                       ( qid )
# 2279 "dlParser.ml"
         in
        
# 243 "<standard.mly>"
    ( x :: xs )
# 2284 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_qid_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.qid list)) = _v in
        let _v : (DlParseTree.qid list) = 
# 144 "<standard.mly>"
    ( x )
# 2294 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_qid__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_s_expression_u : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.expression) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState89 | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAREN ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AND | AS | COMMA | EQ | HAT | OR | ROP4 _ | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.expression)), _startpos_x_) = _menhir_stack in
            let _endpos = _endpos_x_ in
            let _v : (DlParseTree.expressionL list) = let x =
              let x =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2328 "dlParser.ml"
                
              in
              
# 775 "dlParser.mly"
                                             ( x )
# 2334 "dlParser.ml"
              
            in
            
# 221 "<standard.mly>"
    ( [ x ] )
# 2340 "dlParser.ml"
             in
            _menhir_goto_nonempty_list_s_expression_ _menhir_env _menhir_stack _endpos _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89)
    | MenhirState150 | MenhirState145 | MenhirState142 | MenhirState134 | MenhirState127 | MenhirState122 | MenhirState81 | MenhirState82 | MenhirState109 | MenhirState107 | MenhirState105 | MenhirState103 | MenhirState101 | MenhirState99 | MenhirState83 | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_e_, _menhir_s, (e : (DlParseTree.expression)), _startpos_e_) = _menhir_stack in
        let _startpos = _startpos_e_ in
        let _endpos = _endpos_e_ in
        let _v : (DlParseTree.expression) = 
# 742 "dlParser.mly"
                                                     ( e )
# 2356 "dlParser.ml"
         in
        _menhir_goto_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.matchItem list option) = 
# 114 "<standard.mly>"
    ( None )
# 2367 "dlParser.ml"
     in
    _menhir_goto_option_tM_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_instruction_u : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.instruction) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DECODE ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FAIL ->
        _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SEND ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (DlParseTree.instruction)), _startpos_x_) = _menhir_stack in
        let _v : (DlParseTree.instructionL list) = let x =
          let x =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2402 "dlParser.ml"
            
          in
          
# 583 "dlParser.mly"
                                            ( x )
# 2408 "dlParser.ml"
          
        in
        
# 221 "<standard.mly>"
    ( [ x ] )
# 2414 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_instruction_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172

and _menhir_reduce60 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.expressionL list) = 
# 142 "<standard.mly>"
    ( [] )
# 2427 "dlParser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_separated_nonempty_list_DOT_idL_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.qid) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 2441 "dlParser.ml"
        )), _startpos_x_), _endpos__2_, _), _endpos_xs_, _, (xs : (DlParseTree.qid)), _startpos_xs_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : (DlParseTree.qid) = let x =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2457 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 2463 "dlParser.ml"
          
        in
        
# 243 "<standard.mly>"
    ( x :: xs )
# 2469 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_DOT_idL_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState150 | MenhirState145 | MenhirState142 | MenhirState134 | MenhirState127 | MenhirState122 | MenhirState81 | MenhirState82 | MenhirState109 | MenhirState107 | MenhirState105 | MenhirState103 | MenhirState101 | MenhirState99 | MenhirState83 | MenhirState92 | MenhirState89 | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_qid_, _menhir_s, (qid : (DlParseTree.qid)), _startpos_qid_) = _menhir_stack in
        let _startpos = _startpos_qid_ in
        let _endpos = _endpos_qid_ in
        let _v : (DlParseTree.expression) = let qid = 
# 132 "dlParser.mly"
                                       ( qid )
# 2481 "dlParser.ml"
         in
        
# 777 "dlParser.mly"
                                                        ( Id qid   )
# 2486 "dlParser.ml"
         in
        _menhir_goto_s_expression_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState250 | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState250 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState250)
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_qid_, _menhir_s, (qid : (DlParseTree.qid)), _startpos_qid_) = _menhir_stack in
            let _v : (DlParseTree.qid list) = let x = 
# 132 "dlParser.mly"
                                       ( qid )
# 2511 "dlParser.ml"
             in
            
# 241 "<standard.mly>"
    ( [ x ] )
# 2516 "dlParser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_qid_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_stateDef_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.stateDef list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.stateDef))), _, (xs : (DlParseTree.stateDef list))) = _menhir_stack in
        let _v : (DlParseTree.stateDef list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 2539 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_stateDef_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState212 | MenhirState255 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s), _, (sdl : (DlParseTree.stateDef list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.stateDef list) = 
# 376 "dlParser.mly"
                                              ( sdl )
# 2559 "dlParser.ml"
             in
            (match _menhir_s with
            | MenhirState254 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (code : (DlParseTree.stateDef list)) = _v in
                let (((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 2569 "dlParser.ml"
                )), _startpos_x_), (serves : (DlParseTree.qid list))) = _menhir_stack in
                let _1 = () in
                let _v : (DlParseTree.partyDef) = let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2583 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 2589 "dlParser.ml"
                  
                in
                
# 368 "dlParser.mly"
                                                  ( {id=name;serves=serves;code=code} )
# 2595 "dlParser.ml"
                 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (pd : (DlParseTree.partyDef)) = _v in
                let _v : (DlParseTree.subItem) = 
# 341 "dlParser.mly"
                    ( PartyDef   pd  )
# 2603 "dlParser.ml"
                 in
                _menhir_goto_subItem _menhir_env _menhir_stack _menhir_s _v
            | MenhirState211 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (ifBody : (DlParseTree.stateDef list)) = _v in
                let ((((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 2613 "dlParser.ml"
                )), _startpos_x_), _startpos__3_), _endpos__4_, _), _endpos_x_inlined1_, (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 2617 "dlParser.ml"
                )), _startpos_x_inlined1_), _, (advIo : (DlParseTree.id option))) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _3 = () in
                let _1 = () in
                let _v : (DlParseTree.funDef) = let dirIo =
                  let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2635 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 2641 "dlParser.ml"
                  
                in
                let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2655 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 2661 "dlParser.ml"
                  
                in
                
# 301 "dlParser.mly"
                                                                                              ( {id=name; params=[]; idDirIO=dirIo; idAdvIO=advIo; body=[]; stateBody=ifBody} )
# 2667 "dlParser.ml"
                 in
                _menhir_goto_funDef _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_DOT_msgType_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgType list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState236 | MenhirState227 | MenhirState229 | MenhirState181 | MenhirState79 | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (mtl : (DlParseTree.msgType list)) = _v in
        let _v : (DlParseTree.msgPath) = 
# 505 "dlParser.mly"
                                            ( mtl2msgPath mtl )
# 2691 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState181 | MenhirState55 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ARROW ->
                _menhir_reduce117 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63)
        | MenhirState79 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ENCODE ->
                    _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | ID _v ->
                    _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LPAREN ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NOT ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | RPAREN ->
                    _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack) MenhirState81
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState229 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ARROW ->
                _menhir_reduce117 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230)
        | MenhirState236 | MenhirState227 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | ARROW ->
                _menhir_reduce117 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233)
        | _ ->
            _menhir_fail ())
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.msgType list)) = _v in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.msgType))), _endpos__2_) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.msgType list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 2777 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_DOT_msgType_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_terminal : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (DlParseTree.instruction) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (DlParseTree.instruction)) = _v in
    let _startpos_i_ = _startpos in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (DlParseTree.instruction) = 
# 588 "dlParser.mly"
                ( i )
# 2795 "dlParser.ml"
     in
    _menhir_goto_instruction_u _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run82 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RPAREN ->
        _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83

and _menhir_run84 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 2842 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84
    | ID _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AND | AS | COMMA | EQ | HAT | OR | ROP4 _ | RPAREN | SEMICOLON ->
        _menhir_reduce142 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84

and _menhir_run92 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92

and _menhir_goto_msgMatch : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgMatch) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState239
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState239)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_funDef : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.funDef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (fund : (DlParseTree.funDef)) = _v in
    let _v : (DlParseTree.def) = 
# 163 "dlParser.mly"
                  (FunDef fund)
# 2914 "dlParser.ml"
     in
    _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce142 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 26 "dlParser.mly"
       (string)
# 2921 "dlParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 2927 "dlParser.ml"
    )), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (DlParseTree.qid) = let x =
      let idL =
        let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 2942 "dlParser.ml"
        
      in
      
# 129 "dlParser.mly"
              ( idL )
# 2948 "dlParser.ml"
      
    in
    
# 241 "<standard.mly>"
    ( [ x ] )
# 2954 "dlParser.ml"
     in
    _menhir_goto_separated_nonempty_list_DOT_idL_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run86 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 26 "dlParser.mly"
       (string)
# 2961 "dlParser.ml"
) * Lexing.position -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState86 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86

and _menhir_goto_def : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.def) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ADVIO ->
        _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState341
    | DIRIO ->
        _menhir_run287 _menhir_env (Obj.magic _menhir_stack) MenhirState341
    | FUNCT ->
        _menhir_run204 _menhir_env (Obj.magic _menhir_stack) MenhirState341
    | SIM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState341
    | EOF ->
        _menhir_reduce52 _menhir_env (Obj.magic _menhir_stack) MenhirState341
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState341

and _menhir_goto_stateDef : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.stateDef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INITIAL ->
        _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState260
    | STATE ->
        _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState260
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.stateDef))) = _menhir_stack in
        let _v : (DlParseTree.stateDef list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 3014 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_stateDef_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState260

and _menhir_goto_stateDefSim : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.stateDef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INITIAL ->
        _menhir_run195 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | STATE ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | RBRACE ->
        _menhir_reduce56 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState199

and _menhir_goto_msgType : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgType) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_stack = (_menhir_stack, _endpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState61 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OTHERMSG ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61)
    | ARROW | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.msgType))) = _menhir_stack in
        let _v : (DlParseTree.msgType list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 3068 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_DOT_msgType_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce88 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 26 "dlParser.mly"
       (string)
# 3081 "dlParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 3087 "dlParser.ml"
    )), _startpos_x_) = _menhir_stack in
    let _v : (DlParseTree.msgType) = let mT =
      let idL =
        let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3100 "dlParser.ml"
        
      in
      
# 129 "dlParser.mly"
              ( idL )
# 3106 "dlParser.ml"
      
    in
    
# 508 "dlParser.mly"
                   ( MsgType mT       )
# 3112 "dlParser.ml"
     in
    _menhir_goto_msgType _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_nonempty_list_dmessageDef_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.basicIObody) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iob : (DlParseTree.basicIObody)) = _v in
        let _v : (DlParseTree.basicIObody) = 
# 226 "dlParser.mly"
                                     ( iob )
# 3126 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iob : (DlParseTree.basicIObody)) = _v in
        let _v : (DlParseTree.ioBody) = 
# 195 "dlParser.mly"
                        (Basic iob    )
# 3134 "dlParser.ml"
         in
        _menhir_goto_dioBody _menhir_env _menhir_stack _menhir_s _v
    | MenhirState311 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.basicIObody)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.messageDef))) = _menhir_stack in
        let _v : (DlParseTree.basicIObody) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 3145 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_dmessageDef_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run79 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | OTHERMSG ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79

and _menhir_run126 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ENCODE ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAREN ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run141 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 3201 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASGSAMPLE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ENCODE ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState145 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAREN ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState145 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState145)
    | ASGVAL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ENCODE ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ID _v ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAREN ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run148 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__2_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : (DlParseTree.instruction) = 
# 665 "dlParser.mly"
                               ( Fail                  )
# 3269 "dlParser.ml"
         in
        _menhir_goto_terminal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run150 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ENCODE ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150

and _menhir_goto_option_tM_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.matchItem list option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (tupleMatch : (DlParseTree.matchItem list option)) = _v in
        let (_menhir_stack, _menhir_s, (msg : (DlParseTree.msgPath))) = _menhir_stack in
        let _v : (DlParseTree.msgMatch) = 
# 574 "dlParser.mly"
                                       ( {portVar=None; path=msg; tupleMatch=tupleMatch} )
# 3309 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (tupleMatch : (DlParseTree.matchItem list option)) = _v in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 3340 "dlParser.ml"
        )), _startpos_x_), _, (path : (DlParseTree.msgPath))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.msgMatch) = let portConst =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3354 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 3360 "dlParser.ml"
          
        in
        
# 493 "dlParser.mly"
                                                           ( {portVar=Some portConst; path=path; tupleMatch=tupleMatch} )
# 3366 "dlParser.ml"
         in
        _menhir_goto_msgMatch _menhir_env _menhir_stack _menhir_s _v
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (tupleMatch : (DlParseTree.matchItem list option)) = _v in
        let (_menhir_stack, _menhir_s, (path : (DlParseTree.msgPath))) = _menhir_stack in
        let _v : (DlParseTree.msgMatch) = 
# 495 "dlParser.mly"
                                         ( {portVar=None; path=path; tupleMatch=tupleMatch} )
# 3377 "dlParser.ml"
         in
        _menhir_goto_msgMatch _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_subItem_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.subItem list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState265 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.subItem))), _, (xs : (DlParseTree.subItem list))) = _menhir_stack in
        let _v : (DlParseTree.subItem list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 3394 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_subItem_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState285 | MenhirState212 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s), _, (sil : (DlParseTree.subItem list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.subItem list) = 
# 313 "dlParser.mly"
                                                ( sil )
# 3414 "dlParser.ml"
             in
            (match _menhir_s with
            | MenhirState211 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (rfBody : (DlParseTree.subItem list)) = _v in
                let ((((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 3424 "dlParser.ml"
                )), _startpos_x_), _startpos__3_), _endpos__4_, _), _endpos_x_inlined1_, (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 3428 "dlParser.ml"
                )), _startpos_x_inlined1_), _, (advIo : (DlParseTree.id option))) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _3 = () in
                let _1 = () in
                let _v : (DlParseTree.funDef) = let dirIo =
                  let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3446 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 3452 "dlParser.ml"
                  
                in
                let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3466 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 3472 "dlParser.ml"
                  
                in
                
# 299 "dlParser.mly"
                                                                                                ( {id=name; params=[]; idDirIO=dirIo; idAdvIO=advIo; body=rfBody; stateBody=[]} )
# 3478 "dlParser.ml"
                 in
                _menhir_goto_funDef _menhir_env _menhir_stack _menhir_s _v
            | MenhirState284 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (rfBody : (DlParseTree.subItem list)) = _v in
                let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 3488 "dlParser.ml"
                )), _startpos_x_), (parameters : (DlParseTree.funParam list))), _endpos_x_inlined1_, (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 3492 "dlParser.ml"
                )), _startpos_x_inlined1_), _, (advIo : (DlParseTree.id option))) = _menhir_stack in
                let _4 = () in
                let _1 = () in
                let _v : (DlParseTree.funDef) = let dirIo =
                  let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3508 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 3514 "dlParser.ml"
                  
                in
                let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3528 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 3534 "dlParser.ml"
                  
                in
                
# 297 "dlParser.mly"
                                                                                                        ( {id=name; params=parameters; idDirIO=dirIo; idAdvIO=advIo; body=rfBody; stateBody=[]} )
# 3540 "dlParser.ml"
                 in
                _menhir_goto_funDef _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_stateDefSim_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.stateDef list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.stateDef))), _, (xs : (DlParseTree.stateDef list))) = _menhir_stack in
        let _v : (DlParseTree.stateDef list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 3565 "dlParser.ml"
         in
        _menhir_goto_list_stateDefSim_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let (_menhir_stack, _, (sdl : (DlParseTree.stateDef list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.stateDef list) = 
# 554 "dlParser.mly"
                                        ( sdl )
# 3585 "dlParser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (body : (DlParseTree.stateDef list)) = _v in
            let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 3593 "dlParser.ml"
            )), _startpos_x_), _endpos_x_inlined1_, (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 3597 "dlParser.ml"
            )), _startpos_x_inlined1_), _endpos_x_inlined2_, (x_inlined2 : (
# 26 "dlParser.mly"
       (string)
# 3601 "dlParser.ml"
            )), _startpos_x_inlined2_), _, (params : (DlParseTree.id list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.simDef) = let sims =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined2_, _startpos_x_inlined2_, x_inlined2) in
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3618 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 3624 "dlParser.ml"
              
            in
            let uses =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3639 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 3645 "dlParser.ml"
              
            in
            let name =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3659 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 3665 "dlParser.ml"
              
            in
            
# 526 "dlParser.mly"
                                                                                  ( {id=name; uses=uses; sims=sims; simsParamIds=params; body=body } )
# 3671 "dlParser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (simd : (DlParseTree.simDef)) = _v in
            let _v : (DlParseTree.def) = 
# 164 "dlParser.mly"
                  (SimDef simd)
# 3679 "dlParser.ml"
             in
            _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_qid__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.qid list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (xs : (DlParseTree.qid list)) = _v in
    let _1 = () in
    let _v : (DlParseTree.qid list) = let sl = 
# 232 "<standard.mly>"
    ( xs )
# 3700 "dlParser.ml"
     in
    
# 372 "dlParser.mly"
                                        ( sl )
# 3705 "dlParser.ml"
     in
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState254 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INITIAL ->
            _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState255
        | STATE ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState255
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState255)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState254

and _menhir_run85 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 3735 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85
    | AND | AS | COMMA | EQ | HAT | ID _ | LBRACE | LPAREN | OR | ROP4 _ | RPAREN | SEMICOLON ->
        _menhir_reduce142 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85

and _menhir_goto_ioDef : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.ioDef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (iod : (DlParseTree.ioDef)) = _v in
    let _v : (DlParseTree.def) = 
# 162 "dlParser.mly"
                  (IODef iod  )
# 3759 "dlParser.ml"
     in
    _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_loption_separated_nonempty_list_PIPE_msgMatchCode__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgMatchCode list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | END ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__5_ = _endpos in
        let (_menhir_stack, _, (xs : (DlParseTree.msgMatchCode list))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _2 = () in
        let _1 = () in
        let _v : (DlParseTree.msgMatchCode list) = let mmc = 
# 232 "<standard.mly>"
    ( xs )
# 3784 "dlParser.ml"
         in
        
# 486 "dlParser.mly"
                                                                     ( mmc )
# 3789 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s), _, (vars : (DlParseTree.nameType list))), (codes : (DlParseTree.msgMatchCode list))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (DlParseTree.stateCode) = 
# 407 "dlParser.mly"
                                                                    ( {vars=vars; mmcodes=codes} )
# 3808 "dlParser.ml"
             in
            (match _menhir_s with
            | MenhirState222 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (code : (DlParseTree.stateCode)) = _v in
                let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 3818 "dlParser.ml"
                )), _startpos_x_), _startpos__3_), _, (params : (DlParseTree.nameType list))), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _1 = () in
                let _v : (DlParseTree.stateDef) = let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3834 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 3840 "dlParser.ml"
                  
                in
                
# 404 "dlParser.mly"
  ( FollowingState {id=name; params=params; code=code} )
# 3846 "dlParser.ml"
                 in
                _menhir_goto_stateDef _menhir_env _menhir_stack _menhir_s _v
            | MenhirState258 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (code : (DlParseTree.stateCode)) = _v in
                let ((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 3856 "dlParser.ml"
                )), _startpos_x_) = _menhir_stack in
                let _2 = () in
                let _1 = () in
                let _v : (DlParseTree.stateDef) = let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 3871 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 3877 "dlParser.ml"
                  
                in
                
# 402 "dlParser.mly"
  ( InitialState   {id=name; params=[]; code=code}     )
# 3883 "dlParser.ml"
                 in
                _menhir_goto_stateDef _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run228 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 3904 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState229 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | OTHERMSG ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState229 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229)
    | ARROW | DOT | LPAREN ->
        _menhir_reduce88 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_loption_separated_nonempty_list_PIPE_msgMatchCodeSim__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgMatchCode list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | END ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__5_ = _endpos in
        let (_menhir_stack, _, (xs : (DlParseTree.msgMatchCode list))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _2 = () in
        let _1 = () in
        let _v : (DlParseTree.msgMatchCode list) = let mmc = 
# 232 "<standard.mly>"
    ( xs )
# 3954 "dlParser.ml"
         in
        
# 567 "dlParser.mly"
                                                                       ( mmc )
# 3959 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s), _, (vars : (DlParseTree.nameType list))), (codes : (DlParseTree.msgMatchCode list))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (DlParseTree.stateCode) = 
# 564 "dlParser.mly"
                                                                       ( {vars=vars; mmcodes=codes} )
# 3978 "dlParser.ml"
             in
            (match _menhir_s with
            | MenhirState45 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (code : (DlParseTree.stateCode)) = _v in
                let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 3988 "dlParser.ml"
                )), _startpos_x_), _startpos__3_), _, (params : (DlParseTree.nameType list))), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _1 = () in
                let _v : (DlParseTree.stateDef) = let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 4004 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 4010 "dlParser.ml"
                  
                in
                
# 561 "dlParser.mly"
  ( FollowingState {id=name; params=params; code=code} )
# 4016 "dlParser.ml"
                 in
                _menhir_goto_stateDefSim _menhir_env _menhir_stack _menhir_s _v
            | MenhirState197 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (code : (DlParseTree.stateCode)) = _v in
                let ((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 4026 "dlParser.ml"
                )), _startpos_x_) = _menhir_stack in
                let _2 = () in
                let _1 = () in
                let _v : (DlParseTree.stateDef) = let name =
                  let idL =
                    let _endpos = _endpos_x_ in
                    let _startpos = _startpos_x_ in
                    
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 4041 "dlParser.ml"
                    
                  in
                  
# 129 "dlParser.mly"
              ( idL )
# 4047 "dlParser.ml"
                  
                in
                
# 559 "dlParser.mly"
  ( InitialState   {id=name; params=[]; code=code}     )
# 4053 "dlParser.ml"
                 in
                _menhir_goto_stateDefSim _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run56 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let _startpos_x_ = _startpos in
    let x = () in
    let _v : (DlParseTree.msgType) = let l =
      let _endpos = _endpos_x_ in
      let _startpos = _startpos_x_ in
      
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 4088 "dlParser.ml"
      
    in
    
# 509 "dlParser.mly"
                   ( OtherMsg (loc l) )
# 4094 "dlParser.ml"
     in
    _menhir_goto_msgType _menhir_env _menhir_stack _menhir_s _v

and _menhir_run57 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 4101 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce88 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_nonempty_list_amessageDef_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.basicIObody) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState319 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iob : (DlParseTree.basicIObody)) = _v in
        let _v : (DlParseTree.basicIObody) = 
# 229 "dlParser.mly"
                                     ( iob )
# 4118 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iob : (DlParseTree.basicIObody)) = _v in
        let _v : (DlParseTree.ioBody) = 
# 199 "dlParser.mly"
                        (Basic iob    )
# 4126 "dlParser.ml"
         in
        _menhir_goto_aioBody _menhir_env _menhir_stack _menhir_s _v
    | MenhirState329 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.basicIObody)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.messageDef))) = _menhir_stack in
        let _v : (DlParseTree.basicIObody) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 4137 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_amessageDef_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_dmessageDef : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.messageDef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IN ->
        _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState311
    | OUT ->
        _menhir_run290 _menhir_env (Obj.magic _menhir_stack) MenhirState311
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.messageDef))) = _menhir_stack in
        let _v : (DlParseTree.basicIObody) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 4160 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_dmessageDef_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState311

and _menhir_run223 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | VAR ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | MATCH ->
        _menhir_reduce54 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223

and _menhir_run46 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | VAR ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState46
    | MATCH ->
        _menhir_reduce54 _menhir_env (Obj.magic _menhir_stack) MenhirState46
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46

and _menhir_run78 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DECODE ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FAIL ->
        _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ID _v ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IF ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SEND ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78

and _menhir_goto_loption_separated_nonempty_list_COMMA_matchItem__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.matchItem list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__3_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, (xs : (DlParseTree.matchItem list))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (DlParseTree.matchItem list) = let tm = 
# 232 "<standard.mly>"
    ( xs )
# 4238 "dlParser.ml"
         in
        
# 498 "dlParser.mly"
                                                       (tm)
# 4243 "dlParser.ml"
         in
        (match _menhir_s with
        | MenhirState233 | MenhirState230 | MenhirState63 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (DlParseTree.matchItem list)) = _v in
            let _v : (DlParseTree.matchItem list option) = 
# 116 "<standard.mly>"
    ( Some x )
# 4253 "dlParser.ml"
             in
            _menhir_goto_option_tM_ _menhir_env _menhir_stack _menhir_s _v
        | MenhirState157 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (tM : (DlParseTree.matchItem list)) = _v in
            let _v : (DlParseTree.matchItem list) = 
# 626 "dlParser.mly"
                 (  tM  )
# 4263 "dlParser.ml"
             in
            _menhir_goto_decM _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_subItem : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.subItem) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PARTY ->
        _menhir_run246 _menhir_env (Obj.magic _menhir_stack) MenhirState265
    | SUBFUN ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState265
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.subItem))) = _menhir_stack in
        let _v : (DlParseTree.subItem list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 4292 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_subItem_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState265

and _menhir_reduce56 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.stateDef list) = 
# 211 "<standard.mly>"
    ( [] )
# 4305 "dlParser.ml"
     in
    _menhir_goto_list_stateDefSim_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RPAREN ->
                _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState26
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState26)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run195 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STATE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState197
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_COMMA_idL_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.id list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.id list)) = _v in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 4399 "dlParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.id list) = let x =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 4413 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 4419 "dlParser.ml"
          
        in
        
# 243 "<standard.mly>"
    ( x :: xs )
# 4425 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_idL_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.id list)) = _v in
        let _v : (DlParseTree.id list) = 
# 144 "<standard.mly>"
    ( x )
# 4435 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_idL__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run213 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LPAREN ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState216)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s), _, _, _), _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run218 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState220 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RPAREN ->
                _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState220)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run246 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SERVES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState248 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState248 in
                let _v : (DlParseTree.qid list) = 
# 142 "<standard.mly>"
    ( [] )
# 4565 "dlParser.ml"
                 in
                _menhir_goto_loption_separated_nonempty_list_COMMA_qid__ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState248)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run256 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STATE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run223 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState258)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_aioBody : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.ioBody) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__4_ = _endpos in
        let ((_menhir_stack, _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 4639 "dlParser.ml"
        )), _startpos_x_), _, (iob : (DlParseTree.ioBody))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : (DlParseTree.io) = let name =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 4654 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 4660 "dlParser.ml"
          
        in
        
# 191 "dlParser.mly"
                                             ( {id=name; body=iob}:io )
# 4666 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (io : (DlParseTree.io)) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (DlParseTree.ioDef) = 
# 188 "dlParser.mly"
                        (AdversarialIO io)
# 4676 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iod : (DlParseTree.ioDef)) = _v in
        let _v : (DlParseTree.ioDef) = 
# 179 "dlParser.mly"
                      ( iod )
# 4684 "dlParser.ml"
         in
        _menhir_goto_ioDef _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_dioBody : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.ioBody) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__4_ = _endpos in
        let ((_menhir_stack, _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 4710 "dlParser.ml"
        )), _startpos_x_), _, (iob : (DlParseTree.ioBody))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : (DlParseTree.io) = let name =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 4725 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 4731 "dlParser.ml"
          
        in
        
# 185 "dlParser.mly"
                                             ( {id=name; body=iob}:io )
# 4737 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (io : (DlParseTree.io)) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (DlParseTree.ioDef) = 
# 182 "dlParser.mly"
                    (DirectIO io)
# 4747 "dlParser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iod : (DlParseTree.ioDef)) = _v in
        let _v : (DlParseTree.ioDef) = 
# 178 "dlParser.mly"
                      ( iod )
# 4755 "dlParser.ml"
         in
        _menhir_goto_ioDef _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run64 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UNDERSCORE ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState64 in
        let _v : (DlParseTree.matchItem list) = 
# 142 "<standard.mly>"
    ( [] )
# 4781 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_matchItem__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64

and _menhir_goto_list_localVarDecl_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.nameType list list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.nameType list list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.nameType list))) = _menhir_stack in
        let _v : (DlParseTree.nameType list list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 4800 "dlParser.ml"
         in
        _menhir_goto_list_localVarDecl_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState223 | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (lvds : (DlParseTree.nameType list list)) = _v in
        let _v : (DlParseTree.nameType list) = 
# 411 "dlParser.mly"
                             ( List.flatten lvds )
# 4810 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState46 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | MATCH ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | MESSAGE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | WITH ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | ID _v ->
                            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | OTHERMSG ->
                            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | END ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_s = MenhirState55 in
                            let _v : (DlParseTree.msgMatchCode list) = 
# 142 "<standard.mly>"
    ( [] )
# 4844 "dlParser.ml"
                             in
                            _menhir_goto_loption_separated_nonempty_list_PIPE_msgMatchCodeSim__ _menhir_env _menhir_stack _menhir_s _v
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        raise _eRR)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState223 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | MATCH ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | MESSAGE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | WITH ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | ID _v ->
                            _menhir_run228 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | OTHERMSG ->
                            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | END ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_s = MenhirState227 in
                            let _v : (DlParseTree.msgMatchCode list) = 
# 142 "<standard.mly>"
    ( [] )
# 4897 "dlParser.ml"
                             in
                            _menhir_goto_loption_separated_nonempty_list_PIPE_msgMatchCode__ _menhir_env _menhir_stack _menhir_s _v
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        raise _eRR)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_nameType__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.nameType list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (xs : (DlParseTree.nameType list)) = _v in
    let _v : (DlParseTree.nameType list) = let ps = 
# 232 "<standard.mly>"
    ( xs )
# 4933 "dlParser.ml"
     in
    
# 244 "dlParser.mly"
                                       ( ps )
# 4938 "dlParser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState45
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run223 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState292 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos_x_inlined1_ = _endpos in
                    let (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 5017 "dlParser.ml"
                    )) = _v in
                    let _startpos_x_inlined1_ = _startpos in
                    let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 5023 "dlParser.ml"
                    )), _startpos_x_), _startpos__3_), _, (cont : (DlParseTree.nameType list))), _endpos__5_) = _menhir_stack in
                    let _6 = () in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : (DlParseTree.messageDef) = let pl =
                      let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
                      let idL =
                        let _endpos = _endpos_x_ in
                        let _startpos = _startpos_x_ in
                        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5041 "dlParser.ml"
                        
                      in
                      
# 129 "dlParser.mly"
              ( idL )
# 5047 "dlParser.ml"
                      
                    in
                    let name =
                      let idL =
                        let _endpos = _endpos_x_ in
                        let _startpos = _startpos_x_ in
                        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5061 "dlParser.ml"
                        
                      in
                      
# 129 "dlParser.mly"
              ( idL )
# 5067 "dlParser.ml"
                      
                    in
                    
# 234 "dlParser.mly"
                                                               ( {direction = Out; id = name; content=cont; portLabel=Some pl} )
# 5073 "dlParser.ml"
                     in
                    _menhir_goto_dmessageDef _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState301 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 5108 "dlParser.ml"
            )), _startpos_x_), _endpos_x_inlined1_, (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 5112 "dlParser.ml"
            )), _startpos_x_inlined1_), _startpos__5_), _, (cont : (DlParseTree.nameType list))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.messageDef) = let name =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5130 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 5136 "dlParser.ml"
              
            in
            let pl =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5150 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 5156 "dlParser.ml"
              
            in
            
# 233 "dlParser.mly"
                                                               ( {direction = In;  id = name; content=cont; portLabel=Some pl} )
# 5162 "dlParser.ml"
             in
            _menhir_goto_dmessageDef _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState326 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, (dir : (DlParseTree.msgInOut))), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 5185 "dlParser.ml"
            )), _startpos_x_), _startpos__3_), _, (cont : (DlParseTree.nameType list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _v : (DlParseTree.messageDef) = let name =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5200 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 5206 "dlParser.ml"
              
            in
            
# 241 "dlParser.mly"
                                                              ( {direction = dir; id = name; content=cont; portLabel=None} )
# 5212 "dlParser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IN ->
                _menhir_run321 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | OUT ->
                _menhir_run320 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | RBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (DlParseTree.messageDef))) = _menhir_stack in
                let _v : (DlParseTree.basicIObody) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 5229 "dlParser.ml"
                 in
                _menhir_goto_nonempty_list_amessageDef_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState329)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run28 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 26 "dlParser.mly"
       (string)
# 5248 "dlParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState28 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28

and _menhir_goto_decM : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.matchItem list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_COMMA_matchItem_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.matchItem list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.matchItem list)) = _v in
        let _v : (DlParseTree.matchItem list) = 
# 144 "<standard.mly>"
    ( x )
# 5298 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_matchItem__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.matchItem list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.matchItem))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.matchItem list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 5310 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_matchItem_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run65 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let _startpos_x_ = _startpos in
    let x = () in
    let _v : (DlParseTree.matchItem) = let l =
      let _endpos = _endpos_x_ in
      let _startpos = _startpos_x_ in
      
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5333 "dlParser.ml"
      
    in
    
# 503 "dlParser.mly"
                     ( Wildcard (loc l) )
# 5339 "dlParser.ml"
     in
    _menhir_goto_matchItem _menhir_env _menhir_stack _menhir_s _v

and _menhir_run66 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 5346 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack)
    | ARROW | COMMA | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 5360 "dlParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _v : (DlParseTree.matchItem) = let id =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5373 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 5379 "dlParser.ml"
          
        in
        
# 501 "dlParser.mly"
                     ( Const id         )
# 5385 "dlParser.ml"
         in
        _menhir_goto_matchItem _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_STAR_tyBr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.ty list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.ty))), _, (xs : (DlParseTree.ty list))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.ty list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 5407 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_STAR_tyBr_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _, (tuphd : (DlParseTree.ty))), _, (tuptl : (DlParseTree.ty list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.ty) = 
# 271 "dlParser.mly"
                                                                               ( TupleTy (tuphd::tuptl) )
# 5428 "dlParser.ml"
             in
            _menhir_goto_tyBr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (tuphd : (DlParseTree.ty))), _, (tuptl : (DlParseTree.ty list))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.ty) = 
# 267 "dlParser.mly"
                                                               ( TupleTy (tuphd::tuptl) )
# 5445 "dlParser.ml"
         in
        _menhir_goto_ty _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_idL__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.id list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__3_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, (xs : (DlParseTree.id list))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (DlParseTree.id list) = let params = 
# 232 "<standard.mly>"
    ( xs )
# 5470 "dlParser.ml"
         in
        
# 349 "dlParser.mly"
                                                     ( params )
# 5475 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState14 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | INITIAL ->
                    _menhir_run195 _menhir_env (Obj.magic _menhir_stack) MenhirState23
                | STATE ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23
                | RBRACE ->
                    _menhir_reduce56 _menhir_env (Obj.magic _menhir_stack) MenhirState23
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState216 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s), _endpos_x_, (x : (
# 26 "dlParser.mly"
       (string)
# 5511 "dlParser.ml"
            )), _startpos_x_), _endpos__3_, _startpos__3_), _endpos_x_inlined1_, (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 5515 "dlParser.ml"
            )), _startpos_x_inlined1_), _, (params : (DlParseTree.id list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.subFunDecl) = let funName =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5531 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 5537 "dlParser.ml"
              
            in
            let name =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5551 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 5557 "dlParser.ml"
              
            in
            
# 345 "dlParser.mly"
                                                             ( {id=name; funId=funName; funParamIds=params}:subFunDecl )
# 5563 "dlParser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (sfd : (DlParseTree.subFunDecl)) = _v in
            let _v : (DlParseTree.subItem) = 
# 340 "dlParser.mly"
                    ( SubFunDecl sfd )
# 5571 "dlParser.ml"
             in
            _menhir_goto_subItem _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run16 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 5586 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 5609 "dlParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _v : (DlParseTree.id list) = let x =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 5622 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 5628 "dlParser.ml"
          
        in
        
# 241 "<standard.mly>"
    ( [ x ] )
# 5634 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_idL_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_option_idL_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.id option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState211 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | INITIAL ->
                _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | PARTY ->
                _menhir_run246 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | STATE ->
                _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | SUBFUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState212)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211)
    | MenhirState283 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState284 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | PARTY ->
                _menhir_run246 _menhir_env (Obj.magic _menhir_stack) MenhirState285
            | SUBFUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState285
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState285)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState284)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_funParam_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.funParam list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _startpos__1_), _, (fps : (DlParseTree.funParam list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.funParam list) = 
# 305 "dlParser.mly"
                                                                  ( fps )
# 5724 "dlParser.ml"
             in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IMPLEM ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ID _v ->
                        _menhir_run210 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState283 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LBRACE ->
                        _menhir_reduce111 _menhir_env (Obj.magic _menhir_stack) MenhirState283
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState283)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState279 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.funParam))), _, (xs : (DlParseTree.funParam list))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.funParam list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 5778 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_funParam_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.nameType list) = 
# 142 "<standard.mly>"
    ( [] )
# 5789 "dlParser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_COMMA_nameType__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_msgInOut : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.msgInOut) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState326 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RPAREN ->
                _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState326
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState326)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_nonempty_list_ioItem_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.compositeIObody) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iob : (DlParseTree.compositeIObody)) = _v in
        let _v : (DlParseTree.ioBody) = 
# 196 "dlParser.mly"
                                (Composite iob)
# 5846 "dlParser.ml"
         in
        _menhir_goto_dioBody _menhir_env _menhir_stack _menhir_s _v
    | MenhirState309 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.compositeIObody)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.ioItem))) = _menhir_stack in
        let _v : (DlParseTree.compositeIObody) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 5857 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_ioItem_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState319 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (iob : (DlParseTree.compositeIObody)) = _v in
        let _v : (DlParseTree.ioBody) = 
# 200 "dlParser.mly"
                                (Composite iob)
# 5867 "dlParser.ml"
         in
        _menhir_goto_aioBody _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_PIPE_ : _menhir_env -> 'ttv_tail -> (unit option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OK ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState157 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAREN ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UNDERSCORE ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState157 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState157)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce54 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.nameType list list) = 
# 211 "<standard.mly>"
    ( [] )
# 5907 "dlParser.ml"
     in
    _menhir_goto_list_localVarDecl_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run47 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState47 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47

and _menhir_goto_separated_nonempty_list_COMMA_nameType_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.nameType list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState326 | MenhirState301 | MenhirState292 | MenhirState220 | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (DlParseTree.nameType list)) = _v in
        let _v : (DlParseTree.nameType list) = 
# 144 "<standard.mly>"
    ( x )
# 5934 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_nameType__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (DlParseTree.nameType list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (DlParseTree.nameType))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.nameType list) = 
# 243 "<standard.mly>"
    ( x :: xs )
# 5946 "dlParser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_nameType_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run27 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 5955 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_matchItem : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.matchItem) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState70 | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UNDERSCORE ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (DlParseTree.matchItem))) = _menhir_stack in
            let _v : (DlParseTree.matchItem list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 5999 "dlParser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_matchItem_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (mI : (DlParseTree.matchItem))) = _menhir_stack in
        let _v : (DlParseTree.matchItem list) = 
# 627 "dlParser.mly"
                 ( [mI] )
# 6015 "dlParser.ml"
         in
        _menhir_goto_decM _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_tyBr : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.ty) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAREN ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 | MenhirState34 | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAREN ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
        | ARROW | COMMA | RPAREN | SEMICOLON | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (DlParseTree.ty))) = _menhir_stack in
            let _v : (DlParseTree.ty list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 6073 "dlParser.ml"
             in
            _menhir_goto_separated_nonempty_list_STAR_tyBr_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState152 | MenhirState49 | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAREN ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_def_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.def list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, (ext : (DlParseTree.externals))), _, (defs : (DlParseTree.def list))) = _menhir_stack in
            let _3 = () in
            let _v : (
# 117 "dlParser.mly"
       (DlParseTree.dlprog)
# 6126 "dlParser.ml"
            ) = 
# 139 "dlParser.mly"
                                         ( {externals=ext; definitions=defs} )
# 6130 "dlParser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 117 "dlParser.mly"
       (DlParseTree.dlprog)
# 6137 "dlParser.ml"
            )) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState341 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (DlParseTree.def))), _, (xs : (DlParseTree.def list))) = _menhir_stack in
        let _v : (DlParseTree.def list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 6153 "dlParser.ml"
         in
        _menhir_goto_list_def_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState15 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState15 in
        let _v : (DlParseTree.id list) = 
# 142 "<standard.mly>"
    ( [] )
# 6173 "dlParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_idL__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState15

and _menhir_reduce111 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.id option) = 
# 114 "<standard.mly>"
    ( None )
# 6186 "dlParser.ml"
     in
    _menhir_goto_option_idL_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run210 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 6193 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let (x : (
# 26 "dlParser.mly"
       (string)
# 6202 "dlParser.ml"
    )) = _v in
    let _startpos_x_ = _startpos in
    let _v : (DlParseTree.id option) = let x =
      let idL =
        let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6216 "dlParser.ml"
        
      in
      
# 129 "dlParser.mly"
              ( idL )
# 6222 "dlParser.ml"
      
    in
    
# 116 "<standard.mly>"
    ( Some x )
# 6228 "dlParser.ml"
     in
    _menhir_goto_option_idL_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run273 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 6235 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos_x_inlined1_ = _endpos in
            let (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 6257 "dlParser.ml"
            )) = _v in
            let _startpos_x_inlined1_ = _startpos in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 6263 "dlParser.ml"
            )), _startpos_x_) = _menhir_stack in
            let _2 = () in
            let _v : (DlParseTree.funParam) = let idDirIO =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6278 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 6284 "dlParser.ml"
              
            in
            let name =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6298 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 6304 "dlParser.ml"
              
            in
            
# 309 "dlParser.mly"
                                ( {id=name; idDirIO=idDirIO}:funParam )
# 6310 "dlParser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    _menhir_run273 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState279)
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (DlParseTree.funParam))) = _menhir_stack in
                let _v : (DlParseTree.funParam list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 6334 "dlParser.ml"
                 in
                _menhir_goto_separated_nonempty_list_COMMA_funParam_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run290 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState292 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RPAREN ->
                _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState292
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState292)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run297 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ID _v ->
                        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState301 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | RPAREN ->
                        _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState301
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState301)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, _menhir_s), _, _, _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run320 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (DlParseTree.msgInOut) = 
# 238 "dlParser.mly"
       ( Out )
# 6473 "dlParser.ml"
     in
    _menhir_goto_msgInOut _menhir_env _menhir_stack _menhir_s _v

and _menhir_run321 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (DlParseTree.msgInOut) = 
# 237 "dlParser.mly"
       ( In  )
# 6485 "dlParser.ml"
     in
    _menhir_goto_msgInOut _menhir_env _menhir_stack _menhir_s _v

and _menhir_run304 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 6492 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos_x_inlined1_ = _endpos in
            let (x_inlined1 : (
# 26 "dlParser.mly"
       (string)
# 6514 "dlParser.ml"
            )) = _v in
            let _startpos_x_inlined1_ = _startpos in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 6520 "dlParser.ml"
            )), _startpos_x_) = _menhir_stack in
            let _2 = () in
            let _v : (DlParseTree.ioItem) = let ioType =
              let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6535 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 6541 "dlParser.ml"
              
            in
            let name =
              let idL =
                let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6555 "dlParser.ml"
                
              in
              
# 129 "dlParser.mly"
              ( idL )
# 6561 "dlParser.ml"
              
            in
            
# 215 "dlParser.mly"
                                    ( {id=name; ioId=ioType} )
# 6567 "dlParser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run304 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState309 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (DlParseTree.ioItem))) = _menhir_stack in
                let _v : (DlParseTree.compositeIObody) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 6582 "dlParser.ml"
                 in
                _menhir_goto_nonempty_list_ioItem_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState309)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run30 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 6605 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce171 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_ty : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.ty) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 6622 "dlParser.ml"
        )), _startpos_x_), _, (t : (DlParseTree.ty))) = _menhir_stack in
        let _2 = () in
        let _v : (DlParseTree.nameType) = let name =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6636 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 6642 "dlParser.ml"
          
        in
        
# 263 "dlParser.mly"
                              ( {id=name; ty=t} )
# 6648 "dlParser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState157 | MenhirState70 | MenhirState64 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (nt : (DlParseTree.nameType))) = _menhir_stack in
            let _v : (DlParseTree.matchItem) = 
# 502 "dlParser.mly"
                     ( ConstType nt     )
# 6659 "dlParser.ml"
             in
            _menhir_goto_matchItem _menhir_env _menhir_stack _menhir_s _v
        | MenhirState326 | MenhirState301 | MenhirState292 | MenhirState220 | MenhirState192 | MenhirState26 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ID _v ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState192 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState192)
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (DlParseTree.nameType))) = _menhir_stack in
                let _v : (DlParseTree.nameType list) = 
# 241 "<standard.mly>"
    ( [ x ] )
# 6684 "dlParser.ml"
                 in
                _menhir_goto_separated_nonempty_list_COMMA_nameType_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s), _, (lvs : (DlParseTree.id list))), _, (t : (DlParseTree.ty))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.nameType list) = 
# 414 "dlParser.mly"
                                                          ( List.map (fun lv -> {id=lv; ty=t}) lvs )
# 6713 "dlParser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | VAR ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | MATCH ->
                _menhir_reduce54 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | PIPE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let x = () in
                let _v : (unit option) = 
# 116 "<standard.mly>"
    ( Some x )
# 6752 "dlParser.ml"
                 in
                _menhir_goto_option_PIPE_ _menhir_env _menhir_stack _v
            | OK ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _v : (unit option) = 
# 114 "<standard.mly>"
    ( None )
# 6760 "dlParser.ml"
                 in
                _menhir_goto_option_PIPE_ _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce171 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 26 "dlParser.mly"
       (string)
# 6781 "dlParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 6787 "dlParser.ml"
    )), _startpos_x_) = _menhir_stack in
    let _v : (DlParseTree.ty) = let name =
      let idL =
        let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 6800 "dlParser.ml"
        
      in
      
# 129 "dlParser.mly"
              ( idL )
# 6806 "dlParser.ml"
      
    in
    
# 270 "dlParser.mly"
                                                                ( NamedTy name           )
# 6812 "dlParser.ml"
     in
    _menhir_goto_tyBr _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce52 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (DlParseTree.def list) = 
# 211 "<standard.mly>"
    ( [] )
# 6821 "dlParser.ml"
     in
    _menhir_goto_list_def_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | USES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | SIMS ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ID _v ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | LPAREN ->
                            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (((_menhir_stack, _menhir_s), _, _, _), _, _, _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, _menhir_s), _, _, _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run204 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run273 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_s = MenhirState206 in
                let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | IMPLEM ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ID _v ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | ID _v ->
                            _menhir_run210 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | LBRACE ->
                            _menhir_reduce111 _menhir_env (Obj.magic _menhir_stack) MenhirState209
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState209)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (_menhir_stack, _, _menhir_s) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run287 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run304 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState289 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IN ->
                _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState289
            | OUT ->
                _menhir_run290 _menhir_env (Obj.magic _menhir_stack) MenhirState289
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState289)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run317 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run304 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState319 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IN ->
                _menhir_run321 _menhir_env (Obj.magic _menhir_stack) MenhirState319
            | OUT ->
                _menhir_run320 _menhir_env (Obj.magic _menhir_stack) MenhirState319
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState319)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAREN ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29

and _menhir_run38 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 7088 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STAR ->
        _menhir_reduce171 _menhir_env (Obj.magic _menhir_stack)
    | ARROW | COMMA | RPAREN | SEMICOLON | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 7102 "dlParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _v : (DlParseTree.ty) = let name =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 7115 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 7121 "dlParser.ml"
          
        in
        
# 266 "dlParser.mly"
                                                              ( NamedTy name           )
# 7127 "dlParser.ml"
         in
        _menhir_goto_ty _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_option_imps_ : _menhir_env -> 'ttv_tail -> (DlParseTree.id list option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (imps : (DlParseTree.id list option)) = _v in
    let (_menhir_stack, (reqs : (DlParseTree.id list option))) = _menhir_stack in
    let _v : (DlParseTree.externals) = 
# 143 "dlParser.mly"
                                              ( {ecRequirements= (match reqs with | None -> [] | Some r-> r); dlImports = (match imps with | None ->[] | Some i->i )} )
# 7146 "dlParser.ml"
     in
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ADVIO ->
        _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | DIRIO ->
        _menhir_run287 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | FUNCT ->
        _menhir_run204 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | SIM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | EOF ->
        _menhir_reduce52 _menhir_env (Obj.magic _menhir_stack) MenhirState8
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8

and _menhir_goto_nonempty_list_idL_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (DlParseTree.id list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 7178 "dlParser.ml"
        )), _startpos_x_), _, (xs : (DlParseTree.id list))) = _menhir_stack in
        let _v : (DlParseTree.id list) = let x =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 7191 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 7197 "dlParser.ml"
          
        in
        
# 223 "<standard.mly>"
    ( x :: xs )
# 7203 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_idL_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let (_menhir_stack, _, (reqs : (DlParseTree.id list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.id list) = 
# 155 "dlParser.mly"
                                        ( reqs )
# 7223 "dlParser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (DlParseTree.id list)) = _v in
            let _v : (DlParseTree.id list option) = 
# 116 "<standard.mly>"
    ( Some x )
# 7231 "dlParser.ml"
             in
            _menhir_goto_option_reqs_ _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ID _v ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAREN ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState345 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let (_menhir_stack, _, (imps : (DlParseTree.id list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (DlParseTree.id list) = 
# 147 "dlParser.mly"
                                      ( imps )
# 7281 "dlParser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (DlParseTree.id list)) = _v in
            let _v : (DlParseTree.id list option) = 
# 116 "<standard.mly>"
    ( Some x )
# 7289 "dlParser.ml"
             in
            _menhir_goto_option_imps_ _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_reqs_ : _menhir_env -> 'ttv_tail -> (DlParseTree.id list option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IMPORT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState345 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState345)
    | ADVIO | DIRIO | EOF | FUNCT | SIM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (DlParseTree.id list option) = 
# 114 "<standard.mly>"
    ( None )
# 7324 "dlParser.ml"
         in
        _menhir_goto_option_imps_ _menhir_env _menhir_stack _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState345 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState341 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState329 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState326 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState319 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState311 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState309 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState301 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, _, _), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState292 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState285 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState284 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState283 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, _, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState279 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState265 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState258 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState255 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState254 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState250 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState236 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, _, _), _, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState212 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState145 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState103 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, _, _), _, _, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run2 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 26 "dlParser.mly"
       (string)
# 7710 "dlParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState2 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | COLON | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 26 "dlParser.mly"
       (string)
# 7724 "dlParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _v : (DlParseTree.id list) = let x =
          let idL =
            let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 122 "dlParser.mly"
      (
    { pl_desc = x;
      pl_loc  = EcLocation.make _startpos _endpos;
    }
  )
# 7737 "dlParser.ml"
            
          in
          
# 129 "dlParser.mly"
              ( idL )
# 7743 "dlParser.ml"
          
        in
        
# 221 "<standard.mly>"
    ( [ x ] )
# 7749 "dlParser.ml"
         in
        _menhir_goto_nonempty_list_idL_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and prog : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 117 "dlParser.mly"
       (DlParseTree.dlprog)
# 7772 "dlParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | REQUIRES ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ID _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState1 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1)
    | ADVIO | DIRIO | EOF | FUNCT | IMPORT | SIM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (DlParseTree.id list option) = 
# 114 "<standard.mly>"
    ( None )
# 7802 "dlParser.ml"
         in
        _menhir_goto_option_reqs_ _menhir_env _menhir_stack _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR)

# 269 "<standard.mly>"
  

# 7814 "dlParser.ml"
