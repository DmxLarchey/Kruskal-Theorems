(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import Arith Utf8.

From KruskalTrees
  Require Import list_utils idx vec vtree ltree.

Require Import base vtree_embed ltree_embed
               conversions.

Import vec_notations vtree_notations af_notations.

Set Implicit Arguments.

Theorem kruskal_theorem_vtree_afs : afs_kruskal_vtree.
Proof.
  intros U X R H.
  cut (afs (wft (fun _ => X)) (vtree_upto_embed 0 (fun _ => R))).
  + apply afs_mono; auto.
    intros ? ? ? ?; apply vtree_upto_homeo_uniform; auto.
  + apply afs_vtree_upto_embed; auto.
Qed.

Theorem kruskal_theorem_vtree_af : af_kruskal_vtree.
Proof. apply kruskal_vtree_afs_to_af, kruskal_theorem_vtree_afs. Qed.

Theorem kruskal_theorem_ltree_af : af_kruskal_ltree.
Proof. apply kruskal_vtree_to_ltree, kruskal_theorem_vtree_af. Qed.

Theorem kruskal_theorem_ltree_afs : afs_kruskal_ltree.
Proof. apply kruskal_ltree_af_to_afs, kruskal_theorem_ltree_af. Qed.

Section kruskal_as_closure_properties.

  Context {A : Type} {X : rel₁ A} {R : rel₂ A}.

  Theorem afs_vtree_homeo_embed :
        afs X R
      → afs (wft (λ _, X)) (vtree_homeo_embed R).
  Proof. exact (@kruskal_theorem_vtree_afs _ _ _). Qed.

  Theorem af_vtree_homeo_embed :
        af R
      → af (vtree_homeo_embed R).
  Proof. exact (@kruskal_theorem_vtree_af _ _). Qed.

  Theorem afs_ltree_homeo_embed :
        afs X R
      → afs (ltree_fall (λ x _, X x)) (ltree_homeo_embed R).
  Proof. exact (@kruskal_theorem_ltree_afs _ _ _). Qed.

  Theorem af_ltree_homeo_embed :
        af R
      → af (ltree_homeo_embed R).
  Proof. exact (@kruskal_theorem_ltree_af _ _). Qed.

End kruskal_as_closure_properties.

About af_vtree_homeo_embed.
Print Assumptions af_vtree_homeo_embed.

About af_ltree_homeo_embed.
Print Assumptions af_ltree_homeo_embed.

