(* UcExpressions module *)

open UcTypes
open UcSpec
open UcTypedSpec
open EcLocation
open UcUtils

let builtin_operators = IdMap.add "envport" (bool_type,[port_type]) IdMap.empty

let get_op_sig (id:id) : typ*typ list =
	let op = unloc id in
	if (IdMap.mem op builtin_operators) then IdMap.find op builtin_operators else
	if (UcEcInterface.exists_operator op) = false then parse_error (loc id) (Some "Nonexisting operator or function.")
	else UcEcInterface.get_operator_sig op

let check_nullary_op (id:id) : typ =
	let opsig = get_op_sig id in
	if (snd opsig)<>[] then parse_error (loc id) (Some ("Nullary operator expected, operator "^(unloc id)^" has arguments." ))
	else fst opsig

let check_expr_id (sv:qid->typ) (qid:qid) : typ =
	try sv qid	
	with Not_found -> 
		try (
			match qid with
			| id::[] -> check_nullary_op id 
			| _ -> raise Not_found
		    )		
		with Not_found ->
			parse_error (mergelocs qid) (Some ("Nonexisting variable or constant: "^(string_of_i_opath(unlocs qid))))



let rec check_expression (sv:qid->typ) (expr:expression_l) : typ =
	match (unloc expr) with
	| Id id -> check_expr_id sv id
	| Tuple el -> if ((List.length el)=1)
			then (check_expression sv (List.hd el))
			else Ttuple (List.map (fun e -> check_expression sv e) el) 
	| App (fid,el) -> check_sig sv fid el
	| Enc e -> ignore (check_expression sv e); univ_type

and check_sig sv fid el = 
	let op = unloc fid in
	let opsig = get_op_sig fid in
	let tl = snd opsig in
	let farno = List.length tl in
	let arno = List.length el in
	if farno<>arno then parse_error (loc fid) (Some (op^" expects "^(string_of_int farno)^" arguments, "^(string_of_int arno)^" arguments provided"))
	else
	check_sig_types fid sv tl el;
	fst opsig

and check_sig_types (_:id) (sv:qid->typ) (tl:typ list) (el:expression_l list) : unit =
	let tel=List.combine tl el in
	let teli = fst (List.fold_left (fun (l,i) (t,e) ->(((t,e),i)::l,i+1) ) ([],1) tel) in
	let telic = List.filter (fun ((t,_),_) -> match t with Tconstr _ ->true | _->false) teli in
	List.iter 
(fun ((t,e),i) -> let et=(check_expression sv e) in if t<>et then parse_error (loc e) (Some ("Type mismatch for "^(string_of_int i)^". argument. Expected type:" ^ (string_of_typ t) ^". Provided type:"^ (string_of_typ et) ^".")) else ())
	  telic;
	let teliv = List.filter (fun ((t,_),_) -> match t with Tvar _ ->true | _->false) teli in
	List.iter (fun ((t,_),i) ->
			let telivt = List.filter (fun ((t',_),_)-> t'=t ) teliv in
			let e = snd(fst(List.hd telivt)) in
			let te = check_expression sv e in
			List.iter (fun ((_,e'),i') ->
					if te<>(check_expression sv e')
					then parse_error (loc e') (Some ("Type mismatch, "^(string_of_int i)^". and "^(string_of_int i')^". argument must have the same type."))
					else ()
				) telivt
		  ) teliv

let is_distribution (etyp:typ) : bool =
	match etyp with
	| Tconstr ("distr",_) -> true
	| _ -> false

let get_distribution_typ (etyp:typ) : typ =
	match etyp with
	| Tconstr ("distr",dtyp) ->	begin
			match dtyp with 
			| Some t -> t 
			| None -> raise (Failure "Distribution of type None was not expected.")
				end
	| _ -> raise (Failure "Distribution was expected.")
