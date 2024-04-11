(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq 
  Require Import Utf8.

From KruskalTrees
  Require Import idx vec vtree.

Require Import base statements.

Set Implicit Arguments.

Theorem kruskal_vtree_afs_to_af : afs_kruskal_vtree → af_kruskal_vtree.
Proof.
  intros K X R H%af_iff_afs_True%K.
  apply af_iff_afs_True; revert H.
  apply afs_mono; auto.
  intros t _; induction t; apply wft_fix; auto.
Qed.
