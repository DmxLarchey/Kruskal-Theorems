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
  Require Import tactics idx vec vtree.

Require Import base.
Require Export dtree_embed.

Import idx_notations vec_notations vtree_notations
       vtree_embeddings_notations.

Set Implicit Arguments.

#[local] Reserved Notation "l '≤ₕ' m" (at level 70, no associativity, format "l  ≤ₕ  m").

Section vtree_embeddings.

  Variables (A : Type) (Rₕ : rel₂ A).

  Unset Elimination Schemes.

  Inductive vtree_homeo_embed : vtree A → vtree A → Prop :=
    | vtree_homeo_embed_subt t n x (v : vec _ n) i : t ≤ₕ v⦃i⦄ → t ≤ₕ ⟨x|v⟩
    | vtree_homeo_embed_root n x (v : vec _ n) m y (w : vec _ m) : Rₕ x y → vec_embed vtree_homeo_embed v w → ⟨x|v⟩ ≤ₕ ⟨y|w⟩
  where "s ≤ₕ t" := (vtree_homeo_embed s t).

  Set Elimination Schemes.

  Hint Constructors vtree_homeo_embed vtree_upto_embed : core.

  Section vtree_homeo_embed_ind.

    Variable (P : vtree A → vtree A → Prop)
             (HT1 : ∀ t n x (v : vec _ n) i, t ≤ₕ v⦃i⦄ → P t v⦃i⦄ → P t ⟨x|v⟩)
             (HT2 : ∀ n x (v : vec _ n) m y (w : vec _ m), Rₕ x y → vec_embed vtree_homeo_embed v w → vec_embed P v w → P ⟨x|v⟩ ⟨y|w⟩).

    Theorem vtree_homeo_embed_ind : ∀ s t, s ≤ₕ t → P s t.
    Proof.
      refine (fix loop s t D { struct D } := _).
      destruct D as [ t n x v p H1 | n x v m y w H1 H2 ].
      + apply HT1 with (1 := H1); trivial.
        apply loop, H1.
      + apply HT2; trivial.
        clear x y H1; revert H2.
        induction 1; eauto with vec_db.
    Qed.

  End vtree_homeo_embed_ind.

  Hint Resolve vec_fall2_embed : core.

  Fact vtree_product_upto k (R : nat → rel₂ A) :
            (∀ n, k ≤ n → R n ⊆₂ R k)
          → dtree_product_embed R ⊆₂ vtree_upto_embed k R.
  Proof.
    intros H.
    induction 1 as [ | n ]; eauto.
    destruct (le_lt_dec k n); eauto.
  Qed.

  Fact vtree_product_upto_iff k (X : nat → rel₁ A) (R : nat → rel₂ A) :
             (∀ n x, k ≤ n → ¬ X n x)
            → ∀ s t, wft X s → dtree_product_embed R s t ↔ vtree_upto_embed k R s t.
  Proof.
    intros HX s t H; split; intros H1; revert H1 H.
    + induction 1 as [ t n x v p H1 IH1 | n x v y w H1 H2 IH2 ]; intros H; eauto.
      rewrite wft_fix in H; destruct H as (H3 & H4).
      constructor 2; auto.
      * destruct (le_lt_dec k n) as [ Hn | ]; auto.
        now apply HX in H3.
      * intro; apply IH2; auto.
    + induction 1 as [ t n x v p H1 IH1 | n x v y w H1 H2 H3 IH3 | n x v m y w H1 H2 H3 IH3 ];
        intros H; eauto with dtree_db.
      * rewrite wft_fix in H; destruct H.
        constructor 2; auto.
        intros p; apply IH3; auto.
      * rewrite wft_fix in H.
        apply proj1, HX in H; easy.
  Qed.

  Fact vtree_upto_homeo k (R : nat → rel₂ A) :
             (∀n, n ≤ k → R n ⊆₂ Rₕ)
           → vtree_upto_embed k R ⊆₂ vtree_homeo_embed.
  Proof.
    intros H.
    induction 1 as [ | n ? ? ? ? Hn | ]; eauto.
    generalize (lt_le_weak _ _ Hn); intro; eauto.
  Qed.

  Fact vtree_upto_homeo_uniform k :
             vtree_upto_embed k (λ _, Rₕ) ⊆₂ vtree_homeo_embed.
  Proof. apply vtree_upto_homeo; auto. Qed.

  Fact vtree_homeo_upto_uniform : vtree_homeo_embed ⊆₂ vtree_upto_embed 0 (λ _, Rₕ).
  Proof.
    induction 1; eauto.
    constructor 3; auto; tlia.
  Qed.

End vtree_embeddings.

#[global] Hint Constructors vtree_homeo_embed : vtree_db.
