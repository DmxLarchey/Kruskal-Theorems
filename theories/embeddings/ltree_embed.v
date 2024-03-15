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
  Require Import tactics list_utils ltree.

Require Import base.

Import ListNotations ltree_notations.

Set Implicit Arguments.

Create HintDb ltree_db.

#[local] Reserved Notation "l '≤ₚ' m" (at level 70, no associativity, format "l  ≤ₚ  m").
#[local] Reserved Notation "l '≤ₕ' m" (at level 70, no associativity, format "l  ≤ₕ  m").

Section ltree_embeddings.

  Variables (X : Type) (R : rel₂ X).

  Unset Elimination Schemes.

  (* This is the product embedding for Higman's theorem *)

  Inductive ltree_product_embed : ltree X → ltree X → Prop :=
    | ltree_product_embed_subt {s t x l} : t ∈ l → s ≤ₚ t → s ≤ₚ ⟨x|l⟩ₗ
    | ltree_product_embed_root {x l y m} : R x y → Forall2 ltree_product_embed l m → ⟨x|l⟩ₗ ≤ₚ ⟨y|m⟩ₗ
  where "s ≤ₚ t" := (ltree_product_embed s t).

  (* This is the homeomorphic embedding for Kruskal's tree theorem *)

  Inductive ltree_homeo_embed : ltree X → ltree X → Prop :=
    | homeo_embed_subt s t x l : t ∈ l → s ≤ₕ t → s ≤ₕ ⟨x|l⟩ₗ
    | homeo_embed_root x l y m : R x y → list_embed ltree_homeo_embed l m → ⟨x|l⟩ₗ ≤ₕ ⟨y|m⟩ₗ
  where "s ≤ₕ t" := (ltree_homeo_embed s t).

  Set Elimination Schemes.

  Hint Constructors ltree_product_embed ltree_homeo_embed : core.

  Section ltree_product_embed_ind.

    Variables (P : ltree X → ltree X → Prop)

              (HT1 : ∀ {s t x l}, t ∈ l
                                → s ≤ₚ t
                                → P s t
                                → P s ⟨x|l⟩ₗ)

              (HT2 : ∀ {x l y m}, R x y
                                → Forall2 ltree_product_embed l m
                                → Forall2 P l m
                                → P ⟨x|l⟩ₗ ⟨y|m⟩ₗ).

    (** A programming/Agda style proof. Forall2_mono has been rewritten to
        allow for this nested fixpoint *)

    Fixpoint ltree_product_embed_ind s t (Hst : s ≤ₚ t) { struct Hst } : P s t :=
      match Hst with
      | ltree_product_embed_subt H1 H2 => HT1 H1 H2 (ltree_product_embed_ind H2)
      | ltree_product_embed_root H1 H2 => HT2 H1 H2 (Forall2_mono ltree_product_embed_ind H2)
      end.

  End ltree_product_embed_ind.

  Section ltree_homeo_embed_ind.

    Variable (P : ltree X → ltree X → Prop)

             (HT1 : ∀ s t x l, t ∈ l
                             → s ≤ₕ t
                             → P s t
                             → P s ⟨x|l⟩ₗ)

             (HT2 : ∀ x l y m, R x y 
                             → list_embed ltree_homeo_embed l m
                             → list_embed P l m
                             → P ⟨x|l⟩ₗ ⟨y|m⟩ₗ).

    (** A Ltac style proof *)

    Fixpoint ltree_homeo_embed_ind s t (Hst : s ≤ₕ t) : P s t.
    Proof.
      destruct Hst as [ s t x ll H1 H2 | x ll y mm H1 H2 ].
      + apply HT1 with (1 := H1); trivial.
        apply ltree_homeo_embed_ind, H2.
      + apply HT2; trivial.
        now apply list_embed_mono with (1 := ltree_homeo_embed_ind).
    Qed.

  End ltree_homeo_embed_ind.

End ltree_embeddings.

#[global] Hint Constructors ltree_product_embed ltree_homeo_embed : ltree_db.
