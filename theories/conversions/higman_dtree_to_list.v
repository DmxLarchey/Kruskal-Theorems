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
  Require Import tactics list_utils idx vec dtree.

Require Import base notations dtree_embed statements.

Import ListNotations
       idx_notations vec_notations
       dtree_notations
       af_notations.

Set Implicit Arguments.

(** This file is for educational purposes only since
    af_list_embed is already proved as part of the
    Kruskal-Higman project and also this lemma is
    actually used in the proof of Kruskal-Veldman
    hence of afs_veldman_vtree_upto *)

Section list_to_dtree.

  (* From dtrees unit X void* to lists *)

  Variables (X : Type).

  Local Definition unary_family n : Type :=
    match n with
    | 0 => unit
    | 1 => X
    | _ => Empty_set
    end.

  Notation Y := unary_family.
  Notation T := (dtree Y).

  Local Fixpoint dtree_list (t : T) : list X :=
    match t with
    | @dtree_cons _ 0 _ _ => []
    | @dtree_cons _ 1 x v => x :: dtree_list v⦃idx₀⦄
    | @dtree_cons _ _ x _ => @Empty_set_rect _ x
    end.

  Local Fixpoint list_dtree l : T :=
    match l with
    | []   => ⟨tt|∅⟩
    | x::l => ⟨x|list_dtree l##∅⟩
    end.

  Local Fact dtree_list_dtree l : dtree_list (list_dtree l) = l.
  Proof. induction l; simpl; f_equal; auto. Qed.

  Local Fact list_dtree_list_not_needed t : list_dtree (dtree_list t) = t.
  Proof.
    induction t as [ [ | [ | n ] ] x v IHv ]; simpl in *; try easy; f_equal.
    + now destruct x.
    + now vec invert v.
    + vec invert v as ? v; vec invert v.
      now rewrite IHv.
  Qed.

End list_to_dtree.

Section higman_dtree_to_list.

  Hypothesis higman_dtree : af_higman_dtree.

  Variable (X : Type) (R : rel₂ X).

  Notation Y := (unary_family X).
  Notation T := (dtree Y).

  Let RY n : rel₂ (Y n) :=
    match n with
    | 1 => R
    | _ => ⊤₂
    end.

  Local Lemma higman_lemma_af : af R → af (list_embed R).
  Proof.
    intros H.
    cut (af (dtree_product_embed RY)).
    + clear H.
      af rel morph (fun x y => dtree_list x = y).
      * intros l; exists (list_dtree l); rewrite dtree_list_dtree; auto.
      * intros r t ? ? <- <-.
        induction 1 as [ [|[]] x t v p H IH | [|[]] x v y w H IH ]; simpl; auto;
          ( (destruct x; fail) || idx invert all; auto with list_db).
    + apply higman_dtree with (k := 2).
      * intros [|[]] ?; tlia; intros [].
      * intros [|[]] ?; tlia; simpl; auto.
  Qed.

End higman_dtree_to_list.

Theorem higman_dtree_to_list : af_higman_dtree → af_higman_list.
Proof. intros ? ? ? ?; apply higman_lemma_af; auto. Qed.
