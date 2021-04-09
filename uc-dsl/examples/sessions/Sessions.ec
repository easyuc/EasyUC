(* Sessions.ec *)

(* Common EasyCrypt definitions for multi-session functionalities *)

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

type ins = univ.  

(* an iport is a port plus an instance *)

type iport = port * ins.  

(* type of sessions maps, indexed by session ids (integers) *)

type 'a sessions = (int, 'a) SmtMap.fmap.

(* initial (empty) sessions map *)

op init : 'a sessions = SmtMap.empty.
