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
  Require Import list_utils idx vec
                 dtree vtree ltree btree.

Require Import base dtree_embed vtree_embed ltree_embed.

Import af_notations idx_notations vec_notations ltree_notations.

#[local] Notation "x ∊ v" := (@vec_in _ x _ v) (at level 70, no associativity, format "x  ∊  v").

Definition af_higman_list_at {X} (R : rel₂ X) :=
      af R
    → af (list_embed R).

Definition af_higman_list := ∀ X R, @af_higman_list_at X R.

Definition af_higman_dtree_at k {X} (R : forall n, rel₂ (X n)) :=
      (∀n, k ≤ n → X n → False)
    → (∀n, n < k → af (R n))
    → af (dtree_product_embed R).

(* Higman's theorem for dependent vector based trees of arity strictly below k *)
Definition af_higman_dtree k :=
    ∀ X R, @af_higman_dtree_at k X R.

Definition af_kruskal_vtree_at {X} (R : rel₂ X) :=
      af R
    → af (vtree_homeo_embed R).

(* Kruskal's theorem for vector based trees *)
Definition af_kruskal_vtree :=
    ∀ X R, @af_kruskal_vtree_at X R.

Definition afs_kruskal_vtree_upto_at (k : nat) {A} (X : nat → rel₁ A) (R : nat → rel₂ A) :=
      (∀n, k ≤ n → X n = X k)
    → (∀n, k ≤ n → R n = R k)
    → (∀n, n ≤ k → afs (X n) (R n))
    → afs (wft X) (vtree_upto_embed k R).

(* Kruskal's theorem upto for vector based trees *)
Definition afs_kruskal_vtree_upto :=
    ∀ k A X R, @afs_kruskal_vtree_upto_at k A X R.

(* Kruskal's theorem for list based trees *)
Definition af_kruskal_ltree_at {X} (R : rel₂ X) :=
      af R
    → af (ltree_homeo_embed R).

Definition af_kruskal_ltree := ∀ X R, @af_kruskal_ltree_at X R.

(** Below are AFS versions of the above statements *)

Definition afs_higman_dtree_at k {U} {X : nat → rel₁ U} (R : nat → rel₂ U) :=
      (∀n x, k ≤ n → X n x → False)
    → (∀n,   n < k → afs (X n) (R n))
    → afs (wft X) (dtree_product_embed R).

Definition afs_higman_dtree k :=
    ∀ U X R, @afs_higman_dtree_at k U X R.

Definition afs_kruskal_vtree_at {U} {X : rel₁ U} (R : rel₂ U) :=
      afs X R
    → afs (wft (λ _, X)) (vtree_homeo_embed R).

Definition afs_kruskal_vtree :=
    ∀ U X R, @afs_kruskal_vtree_at U X R.

Definition afs_kruskal_ltree_at {U} {X : rel₁ U} (R : rel₂ U) :=
      afs X R
    → afs (ltree_fall (λ x _, X x)) (ltree_homeo_embed R).

Definition afs_kruskal_ltree :=
    ∀ U X R, @afs_kruskal_ltree_at U X R.

Definition vazsonyi_conjecture_bounded k :=
    ∀ R : rel₂ (btree k),
      (∀ r s n (hn : n < k) v, R r s → s ∊ v → R r (btree_cons v hn))
    → (∀ n v m w (hn : n < k) (hm : m < k), vec_forall2 R v w → R (btree_cons v hn) (btree_cons w hm))
    → ∀f, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).

Print vazsonyi_conjecture_bounded.

Definition vazsonyi_conjecture :=
    ∀ X (R : rel₂ (ltree X)),
      (∀ r s x l, R r s → s ∈ l → R r (ltree_cons x l))
    → (∀ x l y m, list_embed R l m → R (ltree_cons x l) (ltree_cons y m))
    → ∀f, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).