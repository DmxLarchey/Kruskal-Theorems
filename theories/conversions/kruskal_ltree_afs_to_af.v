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

Require Import base statements.

Set Implicit Arguments.

Theorem kruskal_ltree_afs_to_af : afs_kruskal_ltree → af_kruskal_ltree.
Proof.
  intros K X R; red in K |- *.
  intros ?%af_iff_afs_True%K; 
  apply af_iff_afs_True; revert H.
  apply afs_mono; auto.
  intros t _.
  induction t; apply ltree_fall_fix; auto.
Qed.
