(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import Utf8.

From KruskalTrees
  Require Import tactics idx vec vtree.

Require Import base vtree_embed conversions.

Import idx_notations vec_notations vtree_notations.

Set Implicit Arguments.

(* We use conversion and Veldman's theorem afs_vtree_upto_embed *)
Theorem higman_theorem_afs k : afs_higman_dtree k.
Proof.
  apply kruskal_vtree_upto_afs_to_higman_dtree_afs.
  intros ? ? ? ?; red; apply afs_vtree_upto_embed.
Qed.

Theorem higman_theorem_af k : af_higman_dtree k.
Proof. apply higman_dtree_afs_to_af, higman_theorem_afs. Qed.

Theorem higman_lemma_af : af_higman_list.
Proof. apply higman_dtree_to_list, higman_theorem_af. Qed.

#[local] Definition arity {X} (r : dtree X) :=
  match r with
  | @dtree_cons _ n _ _ => n
  end.

Section counter_example.

  (** When the breadth is not bounded, Higman product embedding 
      is not almost full *)

  Variable (X : Type) (R : nat → rel₂ X) (x : X).

  Infix "≤ₚ" := (dtree_product_embed R) (at level 70).

  (* l is a leaf of height 0 and 
     t is a tree of height 1 with 1+n sons *) 
  Let l   : vtree X := ⟨x|∅⟩.
  Let t n : vtree X := ⟨x|vec_set (λ _ : idx (S n), l)⟩.


  Local Fact embed_l r : r ≤ₚ l → arity r = 0.
  Proof.
    intros [ (p & ?) | H ]%dtree_product_embed_inv.
    + idx invert p.
    + destruct r as [ n y w ].
      now destruct H as (-> & _).
  Qed.

  (* The only way for t n to embed into t m is n = m *)
  Local Fact embed_t n m : t n ≤ₚ t m → n = m.
  Proof.
    intros [ (p & H) | (e & _) ]%dtree_product_embed_inv.
    + rewrite vec_prj_set in H.
      now apply embed_l in H.
    + tlia.
  Qed.

  (** If X is inhabited then (dtree_product_embed R) 
      is never almost-full when branching is unbounded *)
  Lemma not_af_product_embed : af (dtree_product_embed R) → False.
  Proof. intros (? & ? & ? & ? & ?%embed_t)%(af_good_pair t); tlia. Qed.

End counter_example.

Check not_af_product_embed.

