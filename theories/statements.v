(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import list_utils idx vec
                 dtree vtree ltree btree.

Require Import base dtree_embed vtree_embed ltree_embed.

Import af_notations idx_notations vec_notations ltree_notations.

(** The statement of Higman's lemma for lists *)

Definition af_higman_list :=
    ∀ X (R : rel₂ X),
      af R
    → af (list_embed R).

(** The statement of Higman's theorem for dependent roses trees:
      - sons are collected in vectors at each arity
      - the type of nodes can vary depending on the arity
      - the relation on nodes can vary depending on the arity
      - the type of nodes of arity greater than k (fixed) should be empty
        hence limiting the breadth of those trees to arity k
    In that case, the nested product embedding is AF. *)

Definition af_higman_dtree := 
    ∀ (k : nat) (X : nat → Type) (R : ∀n, rel₂ (X n)),
      (∀n, k ≤ n → X n → False)
    → (∀n, n < k → af (R n))
    → af (dtree_product_embed R).

(** The statement of Kruskal's theorem for vector based uniform roses trees:
      - the type of nodes is independent of the arity
      - the relation between nodes is independent of the arity
    In that case, the homeomorphic embedding is AF. *)

Definition af_kruskal_vtree :=
    ∀ X (R : rel₂ X), af R → af (vtree_homeo_embed R).

(** The statement of Kruskal's theorem for list based roses trees *)

Definition af_kruskal_ltree :=
    ∀ X (R : rel₂ X), af R → af (ltree_homeo_embed R).

(** The statement of Veldman's theorem for uniform well formed rose trees,
    as established in the Kruskal-Veldman project:
      - sons are collected in vectors
      - the type of nodes is independent of the arity
      - but the sub-type of allowed nodes depends on the arity
      - the relation on nodes can vary depending on the arity *)

Definition afs_veldman_vtree_upto :=
    ∀ (k : nat) A (X : nat → rel₁ A) (R : nat → rel₂ A),
      (∀n, k ≤ n → X n = X k)
    → (∀n, k ≤ n → R n = R k)
    → (∀n, n ≤ k → afs (X n) (R n))
    → afs (wft X) (vtree_upto_embed k R).

(** Below are afs versions of the above statements, that is when
    variations on types is replaced by variations on sub-types *)

Definition afs_higman_dtree :=
    ∀ k U (X : nat → rel₁ U) (R : nat → rel₂ U),
      (∀ n x, k ≤ n → X n x → False)
    → (∀n,   n < k → afs (X n) (R n))
    → afs (wft X) (dtree_product_embed R).

Definition afs_kruskal_vtree :=
    ∀ U (X : rel₁ U) (R : rel₂ U),
      afs X R
    → afs (wft (λ _, X)) (vtree_homeo_embed R).

Definition afs_kruskal_ltree :=
    ∀ U (X : rel₁ U) (R : rel₂ U),
      afs X R
    → afs (ltree_fall (λ x _, X x)) (ltree_homeo_embed R).

(** The statement of Vazsonyi's conjecture for vector based undecorated 
    rose trees, of breadth bounded by k *)

#[local] Notation "x ∊ v" := (@vec_in _ x _ v) (at level 70, no associativity, format "x  ∊  v").
#[local] Notation "⟨ v | h ⟩ᵥ" := (btree_cons v h) (at level 0, v at level 200, format "⟨ v | h ⟩ᵥ").

Definition vazsonyi_conjecture_bounded :=
    ∀ k (R : rel₂ (btree k)),
      (∀ s t n (h : n < k) v, t ∊ v → R s t → R s ⟨v|h⟩ᵥ)
    → (∀ n v m w (hₙ : n < k) (hₘ : m < k), vec_forall2 R v w → R ⟨v|hₙ⟩ᵥ ⟨w|hₘ⟩ᵥ)
    → ∀f, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).

(** The statement of Vazsonyi's conjecture for list based (decorated) 
    rose trees, but the decoration is ignored as if X = unit. *)

Definition vazsonyi_conjecture :=
    ∀ X (R : rel₂ (ltree X)),
      (∀ s t x l, t ∈ l → R s t → R s ⟨x|l⟩ₗ)
    → (∀ x l y m, list_embed R l m → R ⟨x|l⟩ₗ ⟨y|m⟩ₗ)
    → ∀f, ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).

