open EcLocation
open EcSymbols
open UcEcSpec

type msg_path_u =
  {inter_id_path : symbol list;  (* inter id path *)
   msg : symbol}                 (* message name *)

type msg_path = msg_path_u located  (* message path *)

(* message and state expressions *)

type 'a msg_expr =
  {path      : msg_path;            (* message path *)
   args      : 'a list located;  (* message arguments *)
   port_expr : 'a option}        (* message destination - port expr *)

type 'a state_expr =
  {id   : psymbol;             (* state to transition to *)
   args : 'a list located}  (* arguments of new state *)

(* instructions *)

type 'a send_and_transition =
  {msg_expr   : 'a msg_expr;    (* message to send *)
   state_expr : 'a state_expr}  (* state to transition to *)

type lhs =  (* left-hand sides *)
  | LHSSimp  of psymbol       (* assign to variable *)
  | LHSTuple of psymbol list  (* assign to tuple of variables *)

type ('a,'b) instruction_u =
  | Assign of lhs * 'a                             (* ordinary assignment *)
  | Sample of lhs * 'a                             (* sampling assignment *)
  | ITE of 'a * ('a,'b) instruction list located * (* if-then-else *)
           ('a,'b) instruction list located option
  | Match of 'a * ('a,'b) match_clause list located(* match instruction *)
  | SendAndTransition of 'a send_and_transition    (* send and transition *)
  | Fail                                           (* failure *)

and ('a,'b) instruction = ('a,'b) instruction_u located

and ('a,'b) match_clause = 'b * ('a,'b) instruction list located
