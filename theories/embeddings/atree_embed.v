(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import list_utils idx vec dtree vtree.

Require Import base.

Import ListNotations
       idx_notations vec_notations
       dtree_notations.

#[local] Reserved Notation "'⟨' x '|' l '⟩ₐ'" (at level 0, l at level 200, format "⟨ x | l ⟩ₐ").
#[local] Reserved Notation "l '≤ₚ' m" (at level 70, no associativity, format "l  ≤ₚ  m").
#[local] Reserved Notation "l '≤ₕ' m" (at level 70, no associativity, format "l  ≤ₕ  m").

Set Implicit Arguments.

Section atree.

  (** In atree X, the arity of the root is dependent on the label at the root *)

  Variables (X : Type) (a : X → nat).

  Unset Elimination Schemes.

  Inductive atree : Type :=
    | atree_cons x : vec atree (a x) → atree.

  Set Elimination Schemes.

  Arguments atree_cons : clear implicits.

  Notation "⟨ x | v ⟩ₐ" := (atree_cons x v).

  Section atree_rect.

    Variables (P : atree → Type)
              (P_cons : ∀ x v, (∀i, P v⦃i⦄) → P ⟨x|v⟩ₐ).

    Fixpoint atree_rect t : P t :=
      match t with
      | ⟨x|v⟩ₐ => P_cons v (λ i, atree_rect v⦃i⦄)
      end.

    Fact atree_rect_fix x v : atree_rect ⟨x|v⟩ₐ = P_cons v (λ i, atree_rect v⦃i⦄).
    Proof. reflexivity. Qed.

  End atree_rect.

  Definition atree_rec (P : _ → Set) := atree_rect P.
  Definition atree_ind (P : _ → Prop) := atree_rect P.

  Unset Elimination Schemes.

  Variable (R : nat → rel₂ X) (T : rel₂ X).

  Inductive atree_product_embed : atree → atree → Prop :=
    | dtree_embed_subt x v s i : s ≤ₚ v⦃i⦄ → s ≤ₚ ⟨x|v⟩ₐ
    | dtree_embed_root x v y w : R (a x) x y → vec_forall2 atree_product_embed v w → ⟨x|v⟩ₐ ≤ₚ ⟨y|w⟩ₐ
  where "s ≤ₚ t" := (atree_product_embed s t).

  Inductive atree_homeo_embed : atree → atree → Prop :=
    | vtree_homeo_embed_subt t x v i : t ≤ₕ v⦃i⦄ → t ≤ₕ ⟨x|v⟩ₐ
    | vtree_homeo_embed_root x v y w : T x y → vec_embed atree_homeo_embed v w → ⟨x|v⟩ₐ ≤ₕ ⟨y|w⟩ₐ
  where "s ≤ₕ t" := (atree_homeo_embed s t).

  Set Elimination Schemes.

  Section atree_product_embed_ind.

    Variables (P : atree → atree → Prop)
              (HT1 : ∀ t x v i,  t ≤ₚ v⦃i⦄
                               → P t v⦃i⦄
                               → P t ⟨x|v⟩ₐ)
              (HT2 : ∀ x v y w,  R (a x) x y
                               → vec_forall2 atree_product_embed v w
                               → vec_forall2 P v w
                               → P ⟨x|v⟩ₐ ⟨y|w⟩ₐ).

    (* Similar to dtree_product_embed_ind *)
    Theorem atree_product_embed_ind : ∀ s t, s ≤ₚ t → P s t.
    Proof.
      refine (fix loop s t D { struct D } := _).
      destruct D as [ t x v p H1 | x v y w H1 H2 ].
      + apply HT1 with (1 := H1); trivial.
        apply loop, H1.
      + apply HT2; trivial.
        revert v w H2; generalize (a x) (a y).
        clear x y H1.
        induction 1; eauto with vec_db.
    Qed.

  End atree_product_embed_ind.

  Section atree_homeo_embed_ind.

    Variable (P : atree → atree → Prop)
             (HT1 : ∀ t x v i, t ≤ₕ v⦃i⦄
                             → P t v⦃i⦄
                             → P t ⟨x|v⟩ₐ)
             (HT2 : ∀ x v y w, T x y
                             → vec_embed atree_homeo_embed v w
                             → vec_embed P v w
                             → P ⟨x|v⟩ₐ ⟨y|w⟩ₐ).

    (* Similar to vtree_homeo_embed_ind *)
    Theorem atree_homeo_embed_ind : ∀ s t, s ≤ₕ t → P s t.
    Proof.
      refine (fix loop s t D { struct D } := _).
      destruct D as [ t x v p H1 | x v y w H1 H2 ].
      + apply HT1 with (1 := H1); trivial.
        apply loop, H1.
      + apply HT2; trivial.
        revert v w H2; generalize (a x) (a y).
        clear x y H1.
        induction 1; eauto with vec_db.
    Qed.

  End atree_homeo_embed_ind.

End atree.

Arguments atree_product_embed {_} a.
Arguments atree_homeo_embed {_} a.
