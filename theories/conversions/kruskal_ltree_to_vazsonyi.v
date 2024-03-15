(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import list_utils ltree.

Require Import base ltree_embed statements.

Import ltree_notations.

Set Implicit Arguments.

Theorem kruskal_ltree_to_vazsonyi : af_kruskal_ltree → vazsonyi_conjecture.
Proof.
  intros H X R HR1 HR2 f.
  apply af_good_pair.
  generalize (H _ _ (@af_True X)); apply af_mono.
  induction 1; simpl; eauto.
Qed.

Print list.
Print ltree.

Locate "_ ∈ _".
Print "∈".

Print list_embed.

Check kruskal_ltree_to_vazsonyi.
Print Assumptions kruskal_ltree_to_vazsonyi.



