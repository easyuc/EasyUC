(* ucTypedSpec.ml *)

(* Typed Specifications *)

open EcLocation
open UcTypes
open UcSpec

module IdMap = Map.Make(String)
module IdSet = Set.Make(String)
module SL = 
	struct
	type t = string list
	let compare = Pervasives.compare
	end
module QidSet = Set.Make(SL)
module QidMap = Map.Make(SL)

let existsId (idMap:'a IdMap.t) (id:string) : bool = 
	IdMap.exists (fun key _ -> key=id) idMap

type typC = (typ * int) located

type messageDefBody = {direction:msgInOut; content: typC IdMap.t; portLabel: id option}

type basicIObodyC = (messageDefBody located) IdMap.t

type ioItemC = id located

type ioBodyC = 
	| Basic of basicIObodyC
	| Composite of ioItemC IdMap.t

type ioC = ioBodyC located

type stateBody = {isInitial:bool; params:typC IdMap.t; vars:typ located IdMap.t; mmcodes:msgMatchCode list}

type stateC = stateBody located

type subFunDeclBody = {funId:string; funParamIds:id list}

type subFunDeclC = subFunDeclBody located

type partyDefBody = {serves:string list located list; code: stateC IdMap.t}

type partyDefC = partyDefBody located

(*either states is an empty map or both subFuns and parties are empty maps*)
type funBody = {params:(ioItemC * int) IdMap.t; idDirIO:string; idAdvIO:string option; subFuns: subFunDeclC IdMap.t; parties: partyDefC IdMap.t; states: stateC IdMap.t}

type funC = funBody located

type simBody = {uses:string; sims:string; simsParamIds: string list; body: stateC IdMap.t}

type simDefC = simBody located

type typed_spec =
	{
	  directIOs            : ioC IdMap.t;
	  adversarialIOs       : ioC IdMap.t;
	  functionalities      : funC IdMap.t;
	  simulators           : simDefC IdMap.t;
	}
