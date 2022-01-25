(* State.ec *)

(* Defines states that appear in the Commitment.uc protocol *)

require import AllCore Distr UCBasicTypes.
require import Pke Cfptp View.

(* Real Committer *)
type committer = [
  C_WaitCommReq
  | C_WaitCorruptionStatus of (View.committer * port * port * bool)
  | C_WaitContinue of (View.committer * port * port * bool * bool)
  | C_WaitCrs of (View.committer * port * port * bool * bool)
  | C_WaitOpenReq of (View.committer * port * port * bool * bool * Cfptp.D * Pke.rand)
  | C_WaitCRS_Corrupted of (View.committer * port * port * bool * bool)
  | C_WaitAdvCommit of (View.committer * port * port * bool * bool)
  | C_WaitOpenReq_Corrupted of (View.committer * port * port * bool * bool)
  | C_WaitAdvOpen of (View.committer * port * port * bool * bool)
  | C_Final of (View.committer * bool)
].

(* Real Verifier *)
type verifier = [
  V_WaitCommit
  | V_WaitCorruptionStatus of (View.verifier * port * port * Cfptp.D * Pke.ciphertext * Pke.ciphertext)
  | V_WaitOpen of (View.verifier * port * port * Cfptp.D * Pke.ciphertext * Pke.ciphertext * bool)
  | V_WaitCrs of (View.verifier * port * port * Cfptp.D * Pke.ciphertext * Pke.ciphertext * bool * bool * Cfptp.D * Pke.rand)
  | V_Final of (View.verifier)
].
