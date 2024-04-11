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
  Require Import idx vec vtree.

Require Import base statements.

Import idx_notations vec_notations
       vtree_notations
       af_notations.

Set Implicit Arguments.

Section vtree_sig_forget.

  (* From vtree (sig X) to vtree U with X : U -> Prop *)

  Variables (U : _) (X : rel₁ U).

  Local Fixpoint vtree_sig_forget (t : vtree (sig X)) : vtree U :=
    match t with
    | ⟨x|v⟩ => ⟨proj1_sig x|vec_map vtree_sig_forget v⟩
    end.

End vtree_sig_forget.

Section kruskal_vtree_af_to_afs.

  Notation forget := (@vtree_sig_forget _ _).

  Hypothesis kruskal : af_kruskal_vtree.

  Theorem kruskal_vtree_af_to_afs : afs_kruskal_vtree.
  Proof.
    intros U X R H%afs_iff_af_sub_rel%kruskal.
    apply afs_iff_af_sub_rel; revert H.
    af rel morph (fun x y => forget x = proj1_sig y).
    + intros (t & Ht); revert t Ht; simpl.
      induction 1 as [ n x v Hx Hv IHv ] using wft_rect.
      vec reif IHv as (w & Hw).
      exists ⟨exist _ x Hx|w⟩; simpl; f_equal.
      now vec ext; vec rew.
    + intros t1 t2 (r1 & H1) (r2 & H2); simpl; intros <- <-.
      clear H1 H2.
      induction 1 as [ t n [x Hx] v p H1 IH1 | n [x Hx] v m [y Hy] w H1 H2 IH2 ]; simpl.
      * constructor 1 with p.
        now vec rew.
      * constructor 2; auto.
        now apply vec_embed_vec_map.
  Qed.

End kruskal_vtree_af_to_afs.

