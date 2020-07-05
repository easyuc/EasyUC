(* ucUtils.ml *)

(* UC DSL Utilities *)

open UcTypechecked
open UcParseTree
open UcLexer
open EcLocation

(*helpers*)
let index (e:'o) (l:'o list) : int =
	let rec indexR (e:'o) (l:'o list) (i:int) =
	match l with
	| [] -> raise Not_found
	| hd::tl -> if hd=e then i else indexR e tl (i+1)
	in
	indexR e l 0

let toList (mapord: ('o * int) IdMap.t) : 'o list =
	let l = IdMap.fold (fun _ v l -> v::l ) mapord [] in
	let lord = List.sort (fun a1 a2 -> (snd a1)-(snd a2)) l in
	List.map (fun a -> fst a) lord

let filterMap (fm:'a-> 'b option) (m:'a IdMap.t) : 'b IdMap.t =
	let flt = IdMap.filter (fun _ def -> match fm def with Some _ -> true| None -> false) m in
	IdMap.map (fun def -> match fm def with Some x -> x | None -> raise (Failure "!impossible!")) flt

let unlocm (lm:'a located IdMap.t) : 'a IdMap.t =
	IdMap.map (fun al -> unloc al) lm

let mergelocs (l:'a located list) : EcLocation.t =
	mergeall(List.map (fun e-> loc e) l)

let dummyloc (o:'a) : 'a located = mk_loc _dummy o

let dummylocl (l: 'a list) : 'a located list = List.map (fun i -> dummyloc i) l

let string_of_IOpath (iop:string list) : string =
	List.fold_left (fun p i -> if p<>"" then p^"."^i else i) "" iop

let string_of_IOpaths (iops: string list list): string =
	List.fold_left (fun s p -> s^"\n"^(string_of_IOpath p)) "" iops

let string_of_stringl (sl:string list) : string =
	List.fold_left (fun sout s -> sout^"\n"^s) "" sl

let qid1_starts_with_qid2 (q1:qid) (q2:qid) : bool =
	List.for_all (fun b->b) 
		(List.mapi (fun i id2 -> 
			match List.nth_opt q1 i with
			| Some id1 -> (unloc id1)=(unloc id2)
			| None -> false
	
		) q2)

let sl1_starts_with_sl2 (sl1:string list) (sl2:string list) : bool =
	List.for_all (fun b->b) 
		(List.mapi (fun i s2 -> 
			match (List.nth_opt sl1 i) with 
			| Some s1 -> s1=s2
			| None -> false
		) sl2)

let get_msg msg = match msg with
		| Some s -> s
		| None -> "No message???"

let print_ParseError(loc,msg) = 
	print_string ("Location"^(EcLocation.tostring loc)^"\nmsg: "^(get_msg msg)^"\n")

let print_ParseError2(loc1,loc2,msg) = 
	print_string ("Location1"^(EcLocation.tostring loc1)^"\nLocation2"^(EcLocation.tostring loc2)^"\nmsg: "^msg^"\n")

let print_LexicalError(loco,msg) = 
	print_string 
	("Location"^
	 (match loco with 
		| Some loc -> EcLocation.tostring loc
		| None     -> ": Location not provided"
	 )^
	"\nmsg: "^msg^"\n")

let printEx (ex:exn) : unit =
	match ex with
	| ParseError(loc, msg) -> print_ParseError(loc, msg)
	| ParseError2(loc1, loc2, msg) -> print_ParseError2(loc1, loc2, msg)
	| LexicalError(loco,msg) -> print_LexicalError(loco,msg)
	| _-> raise ex

(*-------*)
