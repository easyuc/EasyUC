(* Forwarding.ec *)

(* Definitions Supporting Forwarding.uc *)

require import AllCore UCBasicTypes.
require export SmtMap.

(* an instance can encode whatever a port wants/needs

   if the port isn't from a multi-session functionality, it can encode
   an integer, used to distinguish different uses of the Forwarding
   functionality

   if the port is from a multi-session functionality, it could encode
   the pair of the session id plus an integer, used to distinguish
   different uses of the Forwarding functionality in a given
   session *)

type inst = univ.  

(* an iport is a port plus an instance *)

type iport = port * inst.  

(* type of the sessions map, indexed by session ids (integers) *)

type sessions = (int, iport * iport * univ) SmtMap.fmap.

(* initial (empty) sessions map *)

op init : sessions = SmtMap.empty.
