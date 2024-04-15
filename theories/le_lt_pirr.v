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
  Require Import tactics.

Set Implicit Arguments.

Section le_lt_pirr.

  (* le and lt are proof irrelevant *)

  Local Fact le_inv_eq_dep x y (h : x ≤ y) : ∀e : y = x, le_n x = eq_rect y (le x) h _ e.
  Proof.
    destruct h as [ | y h' ]; intros e.
    + now rewrite (eq_refl_nat e).
    + exfalso; lia.
  Qed.

  Local Fact le_inv_le_dep x y' (h : x ≤ y') :
    match y' return x ≤ y' → Prop with
    | 0   => λ _, True
    | S y => λ h, S y = x ∨ ∃h', le_S x y h' = h
    end h.
  Proof. destruct h; [ destruct x | ]; eauto. Qed.

  Fixpoint le_pirr x y (h₁ h₂ : x ≤ y) { struct h₁ } : h₁ = h₂.
  Proof.
    destruct h₁ as [ | y h₁ ].
    + apply le_inv_eq_dep with (e := eq_refl).
    + specialize (le_pirr _ _ h₁). (* Freeze the recursive call on h₁ *)
      destruct (le_inv_le_dep h₂) as [ | (? & []) ].
      * exfalso; lia.
      * now f_equal.
  Qed.

  Definition lt_pirr x y (h₁ h₂ : x < y) : h₁ = h₂ :=
    le_pirr h₁ h₂.

End le_lt_pirr.
