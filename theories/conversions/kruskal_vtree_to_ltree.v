(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import list_utils idx vec vtree ltree.

Require Import base statements.

Import ListNotations
       idx_notations vec_notations
       vtree_notations ltree_notations
       af_notations.

Set Implicit Arguments.

Section vtree_ltree.

  Variable (X : Type).

  Local Definition vtree_ltree (t : vtree X) : ltree X.
  Proof.
    induction t as [ n x v IHv ].
    exact ⟨x|map IHv (idx_list _)⟩ₗ.
  Defined.

  Local Fact vtree_ltree_fix n x (v : vec _ n) :
        vtree_ltree ⟨x|v⟩ = ⟨x|map vtree_ltree (vec_list v)⟩ₗ.
  Proof.
    unfold vtree_ltree at 1.
    rewrite dtree_rect_fix; f_equal.
    now rewrite vec_list_idx, map_map.
  Qed.

  Local Fact vtree_ltree_surj t : { t' | vtree_ltree t' = t }.
  Proof.
    induction t as [ x lt IHt ].
    Forall reif IHt as (l & Hl).
    rewrite Forall2_xchg, <- Forall2_map_left, Forall2_eq in Hl.
    exists ⟨x|list_vec l⟩.
    now rewrite <- Hl, vtree_ltree_fix, vec_list_vec.
  Qed.

End vtree_ltree.

Section kruskal_vtree_to_ltree_at.

  Variable (X : Type) (R : rel₂ X).

  Hypothesis kruskal : @af_kruskal_vtree_at X R.

  Theorem kruskal_vtree_to_ltree_at : af_kruskal_ltree_at R.
  Proof.
    intros HR; generalize (kruskal HR); clear HR.
    af rel morph (fun x y => vtree_ltree x = y).
    + intros t; destruct (vtree_ltree_surj t); eauto.
    + intros t1 t2 ? ? <- <-.
      induction 1 as [ t n x v p H1 IH1 | n x v m y w H1 H2 IH2 ].
      * rewrite vtree_ltree_fix.
        constructor 1 with (vtree_ltree v⦃p⦄); auto.
        apply in_map_iff; exists v⦃p⦄; split; auto.
        apply in_vec_list; eauto.
      * rewrite !vtree_ltree_fix.
        constructor 2; auto.
        clear x y H1 H2; revert IH2.
        induction 1; econstructor; eauto.
  Qed.

End kruskal_vtree_to_ltree_at.

Theorem kruskal_vtree_to_ltree : af_kruskal_vtree → af_kruskal_ltree.
Proof. intros H ? R; generalize (H _ R); apply kruskal_vtree_to_ltree_at. Qed.



