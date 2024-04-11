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

Require Import base vtree_embed ltree_embed statements.

Import vec_notations vtree_notations af_notations.

Set Implicit Arguments.

Theorem kruskal_theorem_vtree_afs : afs_veldman_vtree_upto → afs_kruskal_vtree.
Proof.
  intros V U X R H.
  cut (afs (wft (fun _ => X)) (vtree_upto_embed 0 (fun _ => R))).
  + apply afs_mono; auto.
    intros ? ? ? ?; apply vtree_upto_homeo_uniform; auto.
  + apply afs_vtree_upto_embed; auto.
Qed.
