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
  Require Import tactics idx vec dtree.

Require Import base.

Import idx_notations vec_notations dtree_notations
       dtree_embbedings_notations.

Set Implicit Arguments.

#[local] Reserved Notation "l '≤ₚ' m" (at level 70, no associativity, format "l  ≤ₚ  m").

Section dtree_product_embed.

  Variables (X : nat → Type).

  Section def.

    Variable (R : ∀{k}, X k → X k → Prop).

    (* Coq generates the proper induction principle because there is no nesting here *)

    Inductive dtree_product_embed : dtree X → dtree X → Prop :=
      | dtree_embed_subt k x (v : vec _ k) s i : s ≤ₚ v⦃i⦄ → s ≤ₚ ⟨x|v⟩
      | dtree_embed_root k x (v : vec _ k) y w : R x y → vec_fall2 dtree_product_embed v w → ⟨x|v⟩ ≤ₚ ⟨y|w⟩
    where "s ≤ₚ t" := (dtree_product_embed s t).

    Fact dtree_product_embed_inv r t :
          r ≤ₚ t
        → match t with
          | @dtree_cons _ m y v
              => (∃i, r ≤ₚ v⦃i⦄)
               ∨ match r with
                 | @dtree_cons _ n x u
                     => ∃ e : n = m, R x↺e y ∧ vec_fall2 dtree_product_embed u↺e v
                 end
          end.
    Proof. intros []; simpl; [ left | right ]; eauto; exists eq_refl; auto. Qed.

  End def.

  Hint Constructors dtree_product_embed : core.

  Fact dtree_product_embed_mono (R T : ∀k, X k → X k → Prop) :
         (∀k, R k ⊆₂ T k) → dtree_product_embed R ⊆₂ dtree_product_embed T.
  Proof. induction 2; eauto. Qed.

End dtree_product_embed.

#[global] Hint Constructors dtree_product_embed : dtree_db.

