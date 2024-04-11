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
  Require Import list_utils ltree.

Require Import base statements.

Import ListNotations
       ltree_notations
       af_notations.

Set Implicit Arguments.

Section ltree_sig_forget.

  (* From ltree (sig X) to ltree U with X : U -> Prop *)

  Variables (U : _) (X : rel₁ U).

  Local Fixpoint ltree_sig_forget (t : ltree (sig X)) : ltree U :=
    match t with
    | ⟨x|l⟩ₗ => ⟨proj1_sig x|map ltree_sig_forget l⟩ₗ
    end.

End ltree_sig_forget.

Section kruskal_ltree_af_to_afs.

  Notation forget := (@ltree_sig_forget _ _).

  Hypothesis kruskal : af_kruskal_ltree.

  Theorem kruskal_ltree_af_to_afs : afs_kruskal_ltree.
  Proof.
    intros U X R H%afs_iff_af_sub_rel%kruskal.
    apply afs_iff_af_sub_rel; revert H.
    af rel morph (fun x y => proj1_sig y = forget x).
    + intros (t & Ht); simpl; revert t Ht.
      induction 1 as [ x l H1 H2 IH2 ] using ltree_fall_rect.
      Forall reif IH2 as (m & Hm).
      exists ⟨exist _ x H1|m⟩ₗ; simpl; f_equal.
      now apply Forall2_eq, Forall2_map_right.
    + intros t1 t2 (r1 & H1) (r2 & H2); simpl; intros -> ->.
      clear H1 H2.
      induction 1 as [ s t (x & Hx) l H1 _ IH2
                     | (x & Hx) l (y & Hy) m H1 H2 IH2
                     ]; simpl.
      * constructor 1 with (forget t); auto.
        apply in_map_iff; eauto.
      * constructor 2; auto.
        now apply list_embed_map.
  Qed.

End kruskal_ltree_af_to_afs.

Check kruskal_ltree_af_to_afs.

