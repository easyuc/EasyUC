(* Encodings.ec *)

(* For encoding messages to univ and decoding messages from univ *)

(* Author: Megan Chen *)

require import AllCore Distr UCBasicTypes.
require import Pke_indcpa Cfptp.

op epdp_commit_univ : (port * port * Cfptp.D * Pke_indcpa.ciphertext * Pke_indcpa.ciphertext, univ) epdp.

lemma valid_epdp_commit_univ :
  valid_epdp epdp_commit_univ.
proof.
admit.
qed.

op epdp_open_univ : (port * port * bool * Pke_indcpa.plaintext * Pke_indcpa.rand, univ) epdp.

lemma valid_epdp_open_univ :
  valid_epdp epdp_open_univ.
proof.
admit.
qed.
