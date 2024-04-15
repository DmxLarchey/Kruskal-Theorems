(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Utf8.

From KruskalTrees
  Require Import list_utils idx vec vtree ltree.

Require Import base vtree_embed ltree_embed
               conversions
               kruskal_theorems
               higman_theorems.

Import vec_notations vtree_notations af_notations.

Theorem vazsonyi_theorem_bounded : vazsonyi_conjecture_bounded.
Proof. apply higman_dtree_to_vazsonyi_bounded, higman_theorem_af. Qed.

Theorem vazsonyi_theorem : vazsonyi_conjecture.
Proof. apply kruskal_ltree_to_vazsonyi, kruskal_theorem_ltree_af. Qed.
