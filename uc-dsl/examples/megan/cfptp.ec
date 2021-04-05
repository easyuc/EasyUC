(* cfptp.ec *)

(* Models a claw-free pair of trapdoor permutations *)

require import Distr.

(* Keys *)
type fkey, bkey. (* forward key, backward key *)
(* domain over which the permutation functions operate *)
type D. (* Note: maybe switch this over to group*)

(* CPFTP algorithms *)
(* for this to be a permutation, need that forward/backward are bijections *)
op keygen: (fkey * bkey) distr.         (* Generate forward and backward keys *)
axiom keygen_ll: is_lossless keygen.
pred valid_keys (keys: fkey * bkey) = support keygen keys.
op forw(fk : fkey, x : D, b : bool): D. (* Forward permutation algorithm *)
op back(bk : bkey, y : D, b : bool): D. (* Backward permutation algorithm *)

axiom correctness (fk : fkey, bk : bkey, b : bool, x : D) :
  valid_keys (fk, bk) => back bk (forw fk x b) b = x.

(* Claw-free pair security guarantee: Given f0, f1, the hardness of finding x0, x1 such that f0(x0) = f1(x1) *)
module type ClawFinder = {
  proc find_claw(fk: fkey) : D * D
}.

module CFP(Cf: ClawFinder) = {
  proc main(): bool ={
    var fk: fkey; var bk: bkey;
    var x0, x1 : D;

    (fk, bk) <$ keygen;             (* Generates keys for CFPTP *)
    (x0, x1) <@ Cf.find_claw(fk);  (* Find any claw for the CFPTP *)
    return (forw fk x0 false = forw fk x1 true); (* Cf succeeds when this happens *)
  }
}.
