open EcParsetree
open UcSpecTypedSpecCommon
open UcTypedSpec
open UcMessage
open UcGenEcInterface

(* utils *********************************************************************)

(* params_map_to_list converts ty_index IdMap.t into a list of
name, type pairs. The list is ordered according to the index of ty_index *)
let params_map_to_list (pm : ty_index IdMap.t) : (string * pty) list =
  let bpm = IdMap.bindings pm in
  let bpm = List.map (fun (s,ti) -> (s, ul ti)) bpm in
  let bpm_ord = List.sort (fun (_,(_,i1)) (_,(_,i2)) -> i1-i2) bpm in
  List.map (fun (name,((_,pty),_)) -> (name, pty)) bpm_ord

(* iff ucdsl message declaration has some port, it is a direct message *)
let isdirect (mb : message_body_tyd) : bool =
  match mb.port with
  | None -> false
  | Some _ -> true

(*****************************************************************************)

(* ucdsl strings *************************************************************)
let __self = "_self"
let __adv = "_adv"
let __st = "_st"
let _init = "init"
let _self_ = "self_"
let _adv_ = "adv_"
let _invoke = "invoke"
let _m = "m"
let __m = "_m"
let _r = "r"
let __r = "_r"
let _parties = "parties"
let _dec = "dec"
let _enc = "enc"
let __x = "_x"
let _envport = "envport"
let _UC__IF = "UC__IF"
let _epdp = "epdp"
let _univ = "univ"
let _addr = "addr"
let _port = "port"
let _msg = "msg"
let _pi = "pi"
let __adv_if_pi = "_adv_if_pi"
let __adv_if_pi_gt0 = "_adv_if_pi_gt0"
let _Dir = "Dir"
let _Adv = "Adv"
let _UCBasicTypes = "UCBasicTypes"

let name_record_func (msg_name : string) : string = msg_name^"__func"

let name_record_adv (msg_name : string) : string = msg_name^"__adv"

let name_record (msg_name : string) (param_name : string) : string = msg_name^"_"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)
  
let uc_name (name : string) : string =
  "UC_"^name

let name_epdp_op (mty_name : string) : string = "epdp_"^mty_name

let state_name (name : string) : string = "_State_"^name
(*****************************************************************************)

(* construction of common ucdsl EcParsetree objects **************************)
(* types *)
let addr_pty : pty = named_pty _addr

let port_pty : pty = named_pty _port

let msg_pty : pty = named_pty _msg

let univ_pty : pty = named_pty _univ

(* expressions *)
let pex_Dir = pex_ident _Dir

let pex_Adv = pex_ident _Adv

let pex_m = pex_ident _m

let pex__self = pex_ident __self

let pex__adv = pex_ident __adv

let pex_envport = pex_ident _envport

let pex_app_envport (arg : pexpr) : pexpr =
  pex_app pex_envport [
    pex__self;
    pex__adv;
    arg;
  ]

(* formulas *)  
let pform_Dir = pform_ident _Dir

let pform_Adv = pform_ident _Adv

(*****************************************************************************)

(* uc instruction to ec statement translation ********************************)

(* vals maps local identifiers of values to expressions that return their value
*)
type locals = { 
  vals  : pexpr IdMap.t
}

let init_locals : locals = { vals = IdMap.empty }

let add_val (valname : string) (subst_expr : pexpr) (locals : locals) : locals =
  { vals = IdMap.add valname subst_expr locals.vals }

(* add ucdsl's message pattern to local values*)
let add_pat_vals
  (msgid : string) (*identifier of a variable of a message type*)
  (inter_id_path : string list) (*path of the interface that contains the mesage type*)
  (msgtyname : string) (*name of the message type*)
  (mb : message_body_tyd) (* message body declaration*)
  (port : psymbol option) (* port identifier from the message pattern*)
  (pat_args : pat list option) (*arguments from the message pattern*)
  (locals : locals) : locals =
  let pex_projq_x fieldname = 
    pex_projq (pex_ident msgid) (inter_id_path,fieldname) 
  in
  (* add expression for a port identifier of a (direct) message to locals*)
  let locals =
    begin match port with
    | None -> locals
    | Some psymbol ->
      let fieldname = name_record_dir_port msgtyname mb in
      let sourceport = pex_projq_x fieldname in
      add_val (ul psymbol) sourceport locals
    end in
  (* add expressions for identifiers of data records of a message to locals *)
  match pat_args with
  | None -> locals
  | Some patl -> 
    List.fold_left2
      (fun locals pat_arg memname ->
        match pat_arg with
        | PatWildcard _ -> locals
        | PatId psymbol ->
          let fieldname = name_record msgtyname memname in
          let memex = pex_projq_x fieldname in
          add_val (ul psymbol) memex locals
      )
      locals patl (fst (List.split (params_map_to_list mb.params_map)))

(* interfaces (of an ideal functionality) *)    
type interfaces = {
  di_name : string; (*name of the direct (composite) interface*)
  di      : basic_inter_body_tyd IdMap.t; (*maps name of a basic interface 
  in the direct interface to the body of the basic interface*)
  ai_name : string; (*name of the adversarial (basic) interface*)
  ai      : basic_inter_body_tyd; (*body of the adversarial interface*)
}

let get_message_body 
  (interfaces : interfaces) 
  (inter_id_path : string list) 
  (msgtyname : string) 
  : message_body_tyd =
  match inter_id_path with
  | [name; bin] when name = interfaces.di_name -> 
      IdMap.find msgtyname (IdMap.find bin interfaces.di)
  | [name] when name = interfaces.ai_name -> 
      IdMap.find msgtyname interfaces.ai
  | _ -> failure "impossible, ideal fun cannot have other inter_id_path"

(* mk_message_record_ex
   makes an expression that returns a record of a message type.
   It is used in generation ec code from ucdsl's send and transition instruction
   The values of record fields are filled from variables _self and _adv
   of the functionality module and port and data arguments*)
let mk_message_record_ex
  (inter_id_path : string list) 
  (msgtyname : string)
  (mb : message_body_tyd)
  (port : pexpr option)
  (data : pexpr list)
  : pexpr =
  (*the record field names are fully qualified, pexrfield_iip is the prefix*)
  let pexrfield_iip = pexrfieldq inter_id_path in
  (*__func field gets assigned the port of the functionality itself*)
  let funcfld = pexrfield_iip (name_record_func msgtyname) (pex_ident __self) in  
  let otherfld = 
    match (mb.port, port) with
    | (None, None) -> (*adversarial message has _adv field that gets
    assigned the value of the functionality's _adv variable*)
      pexrfield_iip (name_record_adv msgtyname) (pex_ident __adv)
    | (Some _, Some p) -> (*direct message has a port field that gets
    assigned the value of the port expression*)
      pexrfield_iip (name_record_dir_port msgtyname mb) p
    | _ -> 
      failure "mb.port and port should either both be None or both Some" in
  let pns = fst (List.split (params_map_to_list mb.params_map)) in
  (* assigning data expressions to data fields*)
  let dataflds = List.map2
    (fun pn ex -> pexrfield_iip (name_record msgtyname pn) ex) 
    pns data in
  pex_record None (funcfld::otherfld::dataflds)

(* uc2ec_expr converts ucdsl expressions to ec expressions. 
   The location data is dropped and replaced with a dummy location.
   envport expression gets _self and _adv parameters added.
   Identifiers from ucdsl's message patterns
   are replaced with identifiers in the locals.vals *)
let rec uc2ec_expr (locals : locals) (uc_expr : pexpr) : pexpr =
  let uc_ec_expr = uc2ec_expr locals in
  match ul uc_expr with
  | PEapp (
      {
        pl_loc  = _;
        pl_desc = PEident (
            {
              pl_loc  = _;
              pl_desc = ([], _envport);
            },
            None
          );
      },
      [arg]) -> 
    pex_app_envport (uc_ec_expr arg)
  | PEident (pqsymbol, ptyannoto) ->
    begin match ((ul pqsymbol), ptyannoto) with
    | (([],s), None) when IdMap.mem s locals.vals -> IdMap.find s locals.vals      
    | _ -> dl (PEident (pqsymbol, ptyannoto))
    end
  | PEcast (pexpr, pty) -> 
    dl (PEcast (uc_ec_expr pexpr, pty))
  | PEint    zint -> 
    dl (PEint zint)
  | PEdecimal (zint, (i, zint2)) -> 
    dl (PEdecimal (zint, (i, zint2)))
  | PEapp (pexpr, pexprl) -> 
    dl (PEapp (uc_ec_expr pexpr, List.map uc_ec_expr pexprl))
  | PElet (plpattern, (pexw, ptyo), pexpr) -> 
    dl (PElet (plpattern, (uc_ec_expr pexw, ptyo), uc_ec_expr pexpr))
  | PEtuple  pexprl ->
    dl (PEtuple (List.map uc_ec_expr pexprl))
  | PEif (pexc, pexif, pexel) ->
    dl (PEif (uc_ec_expr pexc, uc_ec_expr pexif, uc_ec_expr pexel))
  | PEmatch (pexpr, patexl) ->
    dl (PEmatch (
      uc_ec_expr pexpr, 
      List.map (fun (pat,ex) -> (pat, uc_ec_expr ex)) patexl))
  | PEforall (ptybindings, pexpr) ->
    dl (PEforall (ptybindings, uc_ec_expr pexpr))
  | PEexists (ptybindings, pexpr) ->
    dl (PEexists (ptybindings, uc_ec_expr pexpr))
  | PElambda (ptybindings, pexpr) ->
    dl (PElambda (ptybindings, uc_ec_expr pexpr))
  | PErecord (pexpro, pexprrl) ->
    let uc_ec_exprr (pexprr : pexpr rfield) : pexpr rfield =
      {
        rf_name  = pexprr.rf_name;
        rf_tvi   = pexprr.rf_tvi;
        rf_value = uc_ec_expr pexprr.rf_value;
      }
    in
    dl (PErecord (pexpro, List.map uc_ec_exprr pexprrl))
  | PEproj (pexpr, pqsymbol) ->
    dl (PEproj (uc_ec_expr pexpr, pqsymbol))
  | PEproji (pexpr, i) ->
    dl (PEproji (uc_ec_expr pexpr, i))
  | PEscope (pqsymbol, pexpr) ->
    dl (PEscope (pqsymbol, uc_ec_expr pexpr))
    
(* conversion of the assignment instruction *)
let uc2ec_ps_assign (locals : locals) (lhs : lhs) (rhs : pexpr) : pinstr =
  let ec_rhs = uc2ec_expr locals rhs in
  match lhs with
  | LHSSimp  ps  -> ps_assign (ul ps) ec_rhs
  | LHSTuple psl -> ps_assignl (List.map (fun ps -> ul ps) psl) ec_rhs

(* conversion of the sample instruction *)  
let uc2ec_ps_sample (locals : locals) (lhs : lhs) (rhs : pexpr) : pinstr =
  let ec_rhs = uc2ec_expr locals rhs in
  match lhs with
  | LHSSimp  ps  -> ps_rnd (ul ps) ec_rhs
  | LHSTuple psl -> ps_rndl (List.map (fun ps -> ul ps) psl) ec_rhs

(* add "UC_" prefix to the first string in the list*)
let uc_inter_path (path : string list) : string list =
 if path = [] then []
 else 
   let hd = uc_name (List.hd path) in
   let tl = List.tl path in
   hd::tl 

(* converts an ucdsl instruction to an ec instruction list *)
let rec uc2ec_stmt (locals : locals) (interfaces : interfaces) (inst : instruction_tyd) : pstmt =
  match ul inst with
  | Assign (lhs, pexpr) -> [uc2ec_ps_assign locals lhs pexpr]
  | Sample (lhs, pexpr) -> [uc2ec_ps_sample locals lhs pexpr]
  | ITE (pexpr, instruction_tyd_ll, instruction_tyd_llo) ->
     ucITE2ec_stmt locals interfaces pexpr instruction_tyd_ll instruction_tyd_llo
  | Match (pexpr, match_clause_tyd_ll) ->
    ucMatch2ec_stmt locals interfaces pexpr match_clause_tyd_ll
  | SendAndTransition send_and_transition_tyd ->
     ucSandT2ec_stmt locals interfaces send_and_transition_tyd
  | Fail -> []
                
and uc_inst_list2ec_stmt 
  (locals : locals)
  (interfaces : interfaces)
  (uc_instll : instruction_tyd list EcLocation.located) 
  : pstmt =
  List.concat (List.map (uc2ec_stmt locals interfaces) (ul uc_instll))
  
and ucITE2ec_stmt (locals : locals) (interfaces : interfaces)
  (cond : pexpr) 
  (if_br : instruction_tyd list EcLocation.located) 
  (else_bro : instruction_tyd list EcLocation.located option)
  : pstmt =
  let cond = uc2ec_expr locals cond in
  let if_br = uc_inst_list2ec_stmt locals interfaces if_br in
  match else_bro with
  | Some else_br ->
    let else_br = uc_inst_list2ec_stmt locals interfaces else_br in
    [ps_if_then_else cond if_br else_br]
  | None ->
    [ps_if_then cond if_br]
    
and ucMatch2ec_stmt (locals : locals) (interfaces : interfaces)
  (value : pexpr) (clauses : match_clause_tyd list EcLocation.located) : pstmt =
  let value = uc2ec_expr locals value in
  let clauses = ul clauses in
  let uc_clause2ec (clause : match_clause_tyd) : ppattern * pstmt =
    let (s, (bs, is)) = clause in
    let sol = (
      List.map (fun (ecid, _) -> 
        let id = EcIdent.name ecid in
        if id = "_"
        then None
        else Some id
      ) bs
    ) in 
    let stmt = uc_inst_list2ec_stmt locals interfaces is in
    (ppattern s sol, stmt)
  in
  let ec_clauses = List.map uc_clause2ec clauses in
  [ps_match value ec_clauses]
    
and ucSandT2ec_stmt 
  (locals : locals)
  (interfaces : interfaces)
  (s_and_t : send_and_transition_tyd) 
  : pstmt =
  let send locals interfaces (msg_ex : msg_expr_tyd) : pinstr =
    let iip = uc_inter_path (ul msg_ex.path).inter_id_path in
    let mtn = (ul msg_ex.path).msg in
    let mb = get_message_body interfaces iip mtn in
    let porto =
      match msg_ex.port_expr with
      | None -> None
      | Some p -> Some (uc2ec_expr locals p) in
    let args = List.map (fun ex -> uc2ec_expr locals ex) (ul msg_ex.args) in
    let msg = mk_message_record_ex iip mtn mb porto args in
    let epdp_path = (iip, name_epdp_op mtn) in
    let encmsg =
      pex_app (pex_proj (pex_pqident (dl (epdp_path))) _enc) [msg] in
    let msgo = pex_app pex_Some [encmsg] in
    ps_assign __r msgo
  in
  let transition (locals : locals) (st_ex : state_expr_tyd ) : pinstr =
    let args = List.map (fun ex -> uc2ec_expr locals ex) (ul st_ex.args) in
    let st_id = state_name (ul st_ex.id) in
    let st = 
      if args = []
      then pex_ident st_id
      else pex_app (pex_ident st_id) args in
    ps_assign __st st
  in
  [ 
    send locals interfaces s_and_t.msg_expr;
    transition locals s_and_t.state_expr;
  ]
  
(*****************************************************************************)

(* generated message types and epdp operators can shadow already existing
   types and operators with same names. We use shadowed record to handle these.
******************************************************************************)

(*the keys of QsMap, TylMap, AppMap, FunMap uniquely determine
named types, tuple types, type applications and function types, respectively*)
module Qs =
  struct
    type t = EcSymbols.qsymbol
    let compare = Stdlib.compare
  end
  
module QsMap = Map.Make(Qs)

module Tyl =
  struct
    type t = pty_r list
    let compare = Stdlib.compare
  end
  
module TylMap = Map.Make(Tyl)

module App =
  struct
    type t = qsymbol * pty_r list
    let compare = Stdlib.compare
  end
  
module AppMap = Map.Make(App)

module Fun =
  struct
    type t = pty_r * pty_r
    let compare = Stdlib.compare
  end
  
module FunMap = Map.Make(Fun)

type shadowed = {
(*used for fully qualified names of types shadowed by a declared message type*)
  types     : pqsymbol IdMap.t;
(*used for fully qualified names of operators shadowed 
by a declared epdp operator for a message type*)
  operators : pqsymbol IdMap.t;
(*used for fully qualified names of epdp stubs for unknown named types*)  
  nonUCepdp_named : pqsymbol QsMap.t;
(*used for fully qualified names of epdp stubs for unknown tuple types*)
  nonUCepdp_tuple : pqsymbol TylMap.t;
(*used for fully qualified names of epdp stubs for unknown type applications*)
  nonUCepdp_appty : pqsymbol AppMap.t;
(*used for fully qualified names of epdp stubs for (unknown) function types*)
  nonUCepdp_funty : pqsymbol FunMap.t;
}
  
let init_shadowed : shadowed = 
  {
    types = IdMap.empty;
    operators = IdMap.empty;
    nonUCepdp_named = QsMap.empty;
    nonUCepdp_tuple = TylMap.empty;
    nonUCepdp_appty = AppMap.empty;
    nonUCepdp_funty = FunMap.empty;
  }

(* used when constructing a message type declaration*)
let add_ty_name (sh : shadowed) (name : string) : shadowed =
  match ty_lookup_opt name with
  | None -> sh
  | Some (path, _) ->
    {
      types = IdMap.add name (dl (EcPath.toqsymbol path)) sh.types;
      operators = sh.operators;
      nonUCepdp_named = sh.nonUCepdp_named;
      nonUCepdp_tuple = sh.nonUCepdp_tuple;
      nonUCepdp_appty = sh.nonUCepdp_appty;
      nonUCepdp_funty = sh.nonUCepdp_funty;
    }

(* adding a message type inside a basic interface theory might shadow
an existing type in the ec environment. If data fields of some message
are of such type we need to fully qualify the name of the type *)    
let rec qualify_ty (sh : shadowed) (pty : pty) : pty =
  let maybe_swap (pqs : pqsymbol) (alt : pqsymbol IdMap.t) : pqsymbol =
    match ul pqs with
    | ([],s) when IdMap.mem s alt -> IdMap.find s alt (*if type name 
    is not qualified we check if it exists in the map, and replace it with the
    fully qualified name from the map*)
    | _ -> pqs (*if type was already qualified we don't need to do anything*)
  in
  let qtyl (ptyl : pty list) =
    List.map (fun p -> qualify_ty sh p) ptyl
  in
  match ul pty with
  | PTnamed pqs ->
    dl (PTnamed (maybe_swap pqs sh.types)) 
  | PTtuple  ptyl ->
    dl (PTtuple (qtyl ptyl))
  | PTapp (pqs, ptyl) ->
    dl (PTapp ((maybe_swap pqs sh.types), (qtyl ptyl)))
  | PTfun (pty1,pty2) ->
    dl (PTfun (qualify_ty sh pty1, qualify_ty sh pty2))
  | _ -> 
    failure "Impossible, only named types, tuples, type applications and functions can show up in message declarations"

(* shorthand for (fully qualified) msg option type.
   Note that both option and msg are valid names for ucdsl message types *)
let option_of_msgty (sh : shadowed) (name : string) : pty=
  let msgty = named_pty name in
  if IdMap.mem _option sh.types 
  then dl (PTapp (IdMap.find _option sh.types,[msgty]))
  else option_of_pty (named_pty name)

(* used when constructing an epdp operator for a message type*)  
let add_op_name (sh : shadowed) (name : string) : shadowed =
  match op_lookup_opt name with
  | None -> sh
  | Some (path, _) ->
    {
      types = sh.types;
      operators = IdMap.add name (dl (EcPath.toqsymbol path)) sh.operators;
      nonUCepdp_named = sh.nonUCepdp_named;
      nonUCepdp_tuple = sh.nonUCepdp_tuple;
      nonUCepdp_appty = sh.nonUCepdp_appty;
      nonUCepdp_funty = sh.nonUCepdp_funty;
    }

(* If an ucdsl message type has the same name as some type from UCBasicTypes,
the generated epdp for this message will shadow an epdp operator
for the UC basic type. In this case we need to fully qualify the name of
the epdp operator for the UC basic type.*)    
let qualify_opname (sh : shadowed) (name : string) : pqsymbol =
  if IdMap.mem name sh.operators
  then IdMap.find name sh.operators
  else pqs name
    
let add_nonUCepdp_namedty (sh : shadowed) 
(opname : string) (name : qsymbol) : shadowed =
  {
    types = sh.types;
    operators = sh.operators;
    nonUCepdp_named = QsMap.add name (pqs opname) sh.nonUCepdp_named;
    nonUCepdp_tuple = sh.nonUCepdp_tuple;
    nonUCepdp_appty = sh.nonUCepdp_appty;
    nonUCepdp_funty = sh.nonUCepdp_funty;
  }

let add_nonUCepdp_tuple (sh : shadowed) 
(opname : string) (tyl : pty_r list) : shadowed =
  {
    types = sh.types;
    operators = sh.operators;
    nonUCepdp_named = sh.nonUCepdp_named;
    nonUCepdp_tuple = TylMap.add tyl (pqs opname) sh.nonUCepdp_tuple;
    nonUCepdp_appty = sh.nonUCepdp_appty;
    nonUCepdp_funty = sh.nonUCepdp_funty;
  }

let add_nonUCepdp_appty (sh : shadowed)
(opname : string) (app : qsymbol) (tyl : pty_r list) : shadowed =
  {
    types = sh.types;
    operators = sh.operators;
    nonUCepdp_named = sh.nonUCepdp_named;
    nonUCepdp_tuple = sh.nonUCepdp_tuple;
    nonUCepdp_appty = AppMap.add (app,tyl) (pqs opname) sh.nonUCepdp_appty;
    nonUCepdp_funty = sh.nonUCepdp_funty; 
  }

let add_nonUCepdp_funty (sh : shadowed)
(opname : string) (pty1 : pty_r) (pty2 : pty_r) : shadowed =
  {
    types = sh.types;
    operators = sh.operators;
    nonUCepdp_named = sh.nonUCepdp_named;
    nonUCepdp_tuple = sh.nonUCepdp_tuple;
    nonUCepdp_appty = sh.nonUCepdp_appty;
    nonUCepdp_funty = FunMap.add (pty1,pty2) (pqs opname) sh.nonUCepdp_funty;  
  }

(*****************************************************************************)

(* construction of epdp for message data *************************************)

(* epdp stubs for types that are not in UCBasicTypes ------------------------*)  
let stub_no = ref 0

(* Every new epdp stub gets a unique name that is also different from names of
   epdp's in UCBasicTypes. Furthermore, the names of epdp stubs start with UC_,
   and since ucdsl identifiers cannot start with UC_, the new name doesn't 
   shadow any other epdp operator that is used when generating ec code. *)
let epdp_stub_prefix() : string =
  stub_no := !stub_no+1;
  "UC_epdp_stub"^(string_of_int !stub_no)
  
let name_lemma_epdp_valid (name : string) : string =
  "valid_"^name

let lemma_epdp (opname : string) : paxiom =
  let f_ve = pform_ident "valid_epdp" in
  let f_e = pform_ident opname in
  let pfrm = pform_app f_ve [f_e] in
  paxiom_lemma (name_lemma_epdp_valid opname) pfrm 

let write_epdp_stub (ppf : Format.formatter) (op : poperator) : string =
  write_operator ppf op;
  let opname = ul op.po_name in
  let le = lemma_epdp opname in
  write_lemma ppf le;
  let lename = ul le.pa_name in
  write_hint_simplify ppf lename;
  write_hint_rewrite ppf _epdp lename;
  opname
(*---------------------------------------------------------------------------*)

(* epdp for named types -----------------------------------------------------*)
let epdp_basicUCnamedty_univ (tyname : qsymbol) : string option =
  let epdp_name (name : string) : string option =
    match name with
    | "unit" -> Some "epdp_unit_univ"
    | "bool" -> Some "epdp_bool_univ"
    | "int"  -> Some "epdp_int_univ"
    | "addr" -> Some "epdp_addr_univ"
    | "port" -> Some "epdp_port_univ"
    | "univ" -> Some "epdp_id"
    | _ -> None
  in
  let qual,name = tyname in
  match qual with
  | ["Top";"UCBasicTypes"] -> epdp_name name
  | ["UCBasicTypes"] -> epdp_name name
  | [] -> epdp_name name
  | _ -> None

let epdp_namedty_stub_name (name : string) : string =
   (epdp_stub_prefix() )^"_"^name
  
let epdp_namedty_op (name : string) : poperator =  
  let opty = PTapp (pqs _epdp, [named_pty name; univ_pty]) in
  abs_oper_pty (epdp_namedty_stub_name name) (dl opty)
  
let epdp_named_non_UC_type (ppf : Format.formatter option) (sh : shadowed) 
(name : qsymbol) : shadowed * pqsymbol =
  let sh = if (QsMap.mem name sh.nonUCepdp_named) then sh else
    let _, n = name in
    let opname = write_epdp_stub (EcUtils.oget ppf) (epdp_namedty_op n) in
    add_nonUCepdp_namedty sh opname name in
  let epdp_op_pqname = QsMap.find name sh.nonUCepdp_named in
  sh, epdp_op_pqname

let epdp_namedty_univ (ppf : Format.formatter option) (sh : shadowed)
(name : qsymbol) : shadowed * pqsymbol  =
  let eno = epdp_basicUCnamedty_univ name in
  match eno with
  | Some en -> sh, (qualify_opname sh en)
  | None -> epdp_named_non_UC_type ppf sh name

(*---------------------------------------------------------------------------*)

(* epdp for tuples ----------------------------------------------------------*)
let epdp_basicUCtuple_name (arity : int) : string option =
  match arity with
  | 2 -> Some "epdp_pair_univ"
  | 3 -> Some "epdp_tuple3_univ"
  | 4 -> Some "epdp_tuple4_univ"
  | 5 -> Some "epdp_tuple5_univ"
  | 6 -> Some "epdp_tuple6_univ"
  | 7 -> Some "epdp_tuple7_univ"
  | 8 -> Some "epdp_tuple8_univ"
  | _ -> None

let epdp_tuple_stub_name (tyl : pty_r list) : string =
  (epdp_stub_prefix ())^"_tuple"^(string_of_int (List.length tyl))

let epdp_tuple_op (tyl : pty_r list) : poperator =
  let name = epdp_tuple_stub_name tyl in
  let epdp_app_ty (pty : pty) =
    dl (PTapp (pqs _epdp, [pty; univ_pty]))
  in
  let tuplety = dl (PTtuple (List.map (fun t-> (dl t)) tyl)) in
  let opty = epdp_app_ty tuplety in
  abs_oper_pty name opty

let epdp_non_UC_tuple (ppf : Format.formatter option) (sh : shadowed)
(tyl : pty_r list): shadowed * pqsymbol  =
  let sh' = if (TylMap.mem tyl sh.nonUCepdp_tuple) then sh else
    let opname = write_epdp_stub (EcUtils.oget ppf) (epdp_tuple_op tyl) in
    add_nonUCepdp_tuple sh opname tyl in
  let epdp_op_pqname = TylMap.find tyl sh'.nonUCepdp_tuple in
  sh', epdp_op_pqname
(*---------------------------------------------------------------------------*)

(* epdp for type applications -----------------------------------------------*)
let epdp_basicUCappty_name (tyname : qsymbol) : string option =
  let epdp_name (name : string) : string option =
  match name with
    | "choice"  -> Some "epdp_choice_univ"
    | "choice3" -> Some "epdp_choice3_univ"
    | "choice4" -> Some "epdp_choice4_univ"
    | "choice5" -> Some "epdp_choice5_univ"
    | "choice6" -> Some "epdp_choice6_univ"
    | "choice7" -> Some "epdp_choice7_univ"
    | "choice8" -> Some "epdp_choice8_univ"
    | "option"  -> Some "epdp_option_univ"
    | "list"    -> Some "epdp_list_univ"
    | _ -> None
  in
  let qual,name = tyname in
  match qual with
  | ["Top";"UCBasicTypes"] -> epdp_name name
  | ["UCBasicTypes"] -> epdp_name name
  | [] -> epdp_name name
  | _ -> None

let epdp_appty_stub_name (app : qsymbol) : string =
  (epdp_stub_prefix ())^"_app_"^(EcSymbols.string_of_qsymbol app)

let epdp_appty_op (app : qsymbol) (tyl : pty_r list) : poperator =
  let name = epdp_appty_stub_name app in
  let epdp_app_ty (pty : pty) =
    dl (PTapp (pqs _epdp, [pty; univ_pty]))
  in
  let app = dl (PTapp ( dl app , (List.map (fun t-> (dl t)) tyl) )) in
  let opty = epdp_app_ty app in
  abs_oper_pty name opty

let epdp_non_UC_appty (ppf : Format.formatter option) (sh : shadowed)
(app : qsymbol) (tyl : pty_r list): shadowed * pqsymbol  =
  let sh' = if (AppMap.mem (app,tyl) sh.nonUCepdp_appty) then sh else
    let opname = write_epdp_stub (EcUtils.oget ppf) (epdp_appty_op app tyl) in
    add_nonUCepdp_appty sh opname app tyl 
  in
  let epdp_op_pqname = AppMap.find (app,tyl) sh'.nonUCepdp_appty in
  sh', epdp_op_pqname
(*---------------------------------------------------------------------------*)

(* epdp for function types --------------------------------------------------*)
let epdp_funty_stub_name () : string =
  (epdp_stub_prefix ())^"_fun"

let epdp_funty_op (pty1 : pty_r) (pty2 : pty_r) : poperator =
  let name = epdp_funty_stub_name() in
  let epdp_app_ty (pty : pty) =
    dl (PTapp (pqs _epdp, [pty; univ_pty]))
  in
  let funty = dl (PTfun (dl pty1 , dl pty2)) in
  let opty = epdp_app_ty funty in
  abs_oper_pty name opty

let epdp_non_UC_funty (ppf : Format.formatter option) (sh : shadowed)
(pty1 : pty_r) (pty2 : pty_r) : shadowed * pqsymbol  =
  let sh' = if (FunMap.mem (pty1,pty2) sh.nonUCepdp_funty) then sh else
    let opname = write_epdp_stub (EcUtils.oget ppf) (epdp_funty_op pty1 pty2)in
    add_nonUCepdp_funty sh opname pty1 pty2 in
  let epdp_op_pqname = FunMap.find (pty1,pty2) sh'.nonUCepdp_funty in
  sh', epdp_op_pqname
(*---------------------------------------------------------------------------*)

(* combining epdps to construct epdp for a type -----------------------------*)
let rec epdp_pty_univ (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (exf_app : 'a -> 'a list -> 'a)
(t : pty) : shadowed * 'a =
  match ul t with
  | PTtuple  ptys -> epdp_tuple_univ ppf sh exf_name exf_app ptys
  | PTnamed  pqs  -> epdp_namedty_univ_ ppf sh exf_name (ul pqs)
  | PTapp (pqs, ptys) -> epdp_app_univ ppf sh exf_name exf_app (ul pqs) ptys
  | PTfun (pty1, pty2) -> epdp_fun_univ ppf sh exf_name (ul pty1) (ul pty2)
  | _ -> failure ("Only tuples, named types, parametric types and functions are supported." )

and epdp_ptyl (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (exf_app : 'a -> 'a list -> 'a)
(tl : pty list) : shadowed * ('a list) =
  List.fold_left ( fun (sh, l) t ->
    let qt = qualify_ty sh t in
    let sh', e = epdp_pty_univ ppf sh exf_name exf_app qt in
    sh', l@[e]
  ) (sh,[]) tl
  
and epdp_namedty_univ_ (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (name : qsymbol) : shadowed * 'a =
  let sh, pqopname = epdp_namedty_univ ppf sh name in
  sh, exf_name pqopname
  
and epdp_tuple_univ (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (exf_app : 'a -> 'a list -> 'a)
(ptys : pty list) : shadowed * 'a =
  let tyl = ull ptys in
  let arity = List.length tyl in
  let eno = epdp_basicUCtuple_name arity in
  match eno with
  | Some en ->
    let sh', exfl = epdp_ptyl ppf sh exf_name exf_app ptys in
    let epdp_name = qualify_opname sh en in
    sh', exf_app (exf_name epdp_name) exfl
  | None -> 
    let sh', epdp_name = epdp_non_UC_tuple ppf sh tyl in
    sh', exf_name epdp_name

and epdp_app_univ (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (exf_app : 'a -> 'a list -> 'a)
(app : qsymbol) (ptys : pty list) : shadowed * 'a =
  let tyl = ull ptys in
  let eno = epdp_basicUCappty_name app in
  match eno with
  | Some en ->
    let sh', exfl = epdp_ptyl ppf sh exf_name exf_app ptys in
    let epdp_name = qualify_opname sh en in
    sh', exf_app (exf_name epdp_name) exfl
  | None -> 
    let sh', epdp_name = epdp_non_UC_appty ppf sh app tyl in
    sh', exf_name epdp_name

and epdp_fun_univ (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (pty1 : pty_r) (pty2 : pty_r) : shadowed * 'a =
  let sh', epdp_name = epdp_non_UC_funty ppf sh pty1 pty2 in
  sh', exf_name epdp_name
(*---------------------------------------------------------------------------*)

(* epdp_data_univ creates an epdp for message data.
   It is called when constructing enc operator for a message type 
   and lemma eq_of_valid_... for a message type.
   
   The enc operator is constructed first, and if some of the message data 
   has a new type that is not in UCBasicTypes, an epdp stub for this type
   is constructed. In this case, the identifier for this epdp operator is
   added to the sh record, and the stub is written to the file using ppf
   (ppf cannot be None in this case).
   When the lemma is constructed, all of the epdp operators for 
   message data are already in the sh record or in UCBasicTypes, 
   so ppf can be None, and the returned shadowed record is the same as sh.
   
   For the construction of enc operator we need an expression that applies
   enc of the message data epdp to the message parameters, and for the lemma we
   need a formula. 
   The exf_name parameter determines the return type of epdp_data_univ.
   For the enc operator exf_name is a function that maps 
   epdp identifiers into expressions (pex_pqident), 
   and for the lemma into formulas (pform_pqident).
   Similarly, for application of epdp operators to other epdp operators
   we need exf_app, a function that maps expression/formula applied to a list 
   of expressions/formulas into an expression/formula when constructing the 
   enc operator/lemma. *)    
let epdp_data_univ (ppf : Format.formatter option) (sh : shadowed) 
(exf_name : pqsymbol -> 'a) (exf_app : 'a -> 'a list -> 'a)
(params_map : ty_index IdMap.t) : shadowed * 'a =
  let ptys = List.map (fun (_,pty) -> pty) (params_map_to_list params_map) in
  match ptys with
  | [] -> sh, exf_name (qualify_opname sh "epdp_unit_univ") 
  | [t] -> epdp_pty_univ ppf sh exf_name exf_app t
  | _ -> epdp_tuple_univ ppf sh exf_name exf_app ptys

(* enc_u constructs expression that encodes message data, 
   called when constructing enc operator for the message type. *)  
let enc_u (ppf : Format.formatter option) (sh : shadowed) 
(var_name : string) (msg_name : string) (params_map : ty_index IdMap.t) 
: shadowed * pexpr =
  let enc_args (var_name : string) (msg_name : string ) (params_map : ty_index IdMap.t) : pexpr =
    let pns = fst (List.split (params_map_to_list params_map)) in
    if pns = []
    then pex_unit
    else pex_tuple (List.map (fun pn -> pex_proj (pex_ident var_name) (name_record msg_name pn)) pns)
  in
  let sh', ex = epdp_data_univ ppf sh pex_pqident pex_app params_map in
  let ex = pex_proj ex "enc" in
  let args = enc_args var_name msg_name params_map in
  sh', pex_app ex [args]

(* enc_u_form constructs formula that encodes message data, 
   called when constructing lemma eq_of_valid_... for the message type. *)
let enc_u_form (sh : shadowed) (var_name : string) (msg_name : string) (params_map : ty_index IdMap.t) : pformula =
  let enc_args_form (var_name : string) (msg_name : string ) (params_map : ty_index IdMap.t) : pformula =
    let pns = fst (List.split (params_map_to_list params_map)) in
    if pns = []
    then pform_unit
    else pform_tuple (List.map (fun pn -> pform_proj (pform_ident var_name) (name_record msg_name pn)) pns)
  in
  let _, epdp_data_form = epdp_data_univ None sh pform_pqident pform_app params_map in
  let f = pform_proj epdp_data_form "enc" in
  let args = enc_args_form var_name msg_name params_map in
  pform_app f [args]
 
 (****************************************************************************)
