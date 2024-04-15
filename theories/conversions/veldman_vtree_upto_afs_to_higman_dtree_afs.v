(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia Utf8.

From KruskalTrees
  Require Import dtree vtree.

Require Import base notations
               dtree_embed vtree_embed
               statements.

Import vtree_notations dtree_notations.

Set Implicit Arguments.

Theorem veldman_vtree_upto_afs_to_higman_dtree_afs :
      afs_veldman_vtree_upto → afs_higman_dtree.
Proof.
  intros Kr k U X R H1 H2.
  set (X' i := if le_lt_dec k i then ⊥₁ else X i).
  set (R' i := if le_lt_dec k i then ⊥₂ else R i).
  cut (afs (wft X') (vtree_upto_embed k R')).
  af rel morph eq.
  + intros t Ht; exists t; split; auto.
    revert t Ht; apply wft_mono.
    intros n; unfold X'.
    destruct (le_lt_dec k n); eauto.
  + intros ? ? s t ? ? ? ? -> ->.
    rewrite -> vtree_product_upto_iff; eauto.
    apply vtree_upto_embed_mono.
    intros n Hn; unfold R'.
    destruct (le_lt_dec k n); now auto.
  + apply Kr.
    * intros n Hn; unfold X'.
      destruct (le_lt_dec k n); [ | lia ].
      destruct (le_lt_dec k k); auto; lia.
    * intros n Hn; unfold R'.
      destruct (le_lt_dec k n); [ | lia ].
      destruct (le_lt_dec k k); auto; lia.
    * intros n Hn; unfold X', R'.
      destruct (le_lt_dec k n); auto.
Qed.
