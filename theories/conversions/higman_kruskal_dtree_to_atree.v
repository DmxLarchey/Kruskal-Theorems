(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import Arith Lia Utf8.

From KruskalTrees
  Require Import tactics idx vec dtree vtree.

Require Import base
               dtree_embed vtree_embed atree_embed
               statements.

Import idx_notations vec_notations
       dtree_notations
       af_notations.

#[local] Reserved Notation "'⟨' x '|' l '⟩ₐ'" (at level 0, l at level 200, format "⟨ x | l ⟩ₐ").
#[local] Reserved Notation "l '≤ₚ' m" (at level 70, no associativity, format "l  ≤ₚ  m").
#[local] Reserved Notation "l '≤ₕ' m" (at level 70, no associativity, format "l  ≤ₕ  m").

Set Implicit Arguments.

Section vtree_atree.

  Variables (X : Type) (a : X → nat).

  Notation A := (λ n x, n = a x).

  Notation "⟨ x | v ⟩ₐ" := (atree_cons x v).

  Implicit Type (t : atree a).

  Section atree_dtree.

    (* We build a bijection between

            atree a <~~> dtree (fun n => sig (A n))

       Easy in this case *)

    Implicit Type (s : dtree (λ n, sig (A n))).

    Fixpoint atree_dtree (t : atree a) : dtree (λ n, sig (A n)) :=
      match t with
      | ⟨x|v⟩ₐ => ⟨exist _ x eq_refl|vec_map atree_dtree v⟩
      end.

    Fixpoint dtree_atree (s : dtree (λ n, sig (A n))) : atree a :=
      match s with
      | ⟨exist _ x e|v⟩ => ⟨x|vec_map dtree_atree v↺e⟩ₐ
      end.

    Fact dtree_atree_dtree t : dtree_atree (atree_dtree t) = t.
    Proof.
      induction t; simpl; f_equal.
      rewrite vec_map_map; now vec ext; vec rew.
    Qed.

    Fact atree_dtree_atree s : atree_dtree (dtree_atree s) = s.
    Proof.
      induction s as [ ? [] ]; simpl; eq refl; f_equal.
      rewrite vec_map_map; now vec ext; vec rew.
    Qed.

  End atree_dtree.

  Section atree_vtree.

    (* Writing the correspondence between

            { s : vtree X | wft A s } <~~> atree

       is too complicated because of the wft A proofs part.
       The wft A part is required because otherwise, we do not
       have a corresponding atree when arities do not respect A.

       We prefer to describe this bijective correspondance
       as an inductive relation which is much easier to handle
       in this dependent case *)

    Inductive va_tree_eq : vtree X → atree a → Prop :=
      | in_va_tree_eq x (v : vec _ (a x)) w :
                vec_fall2 va_tree_eq v w
              → va_tree_eq ⟨x|v⟩ ⟨x|w⟩ₐ.

    Fact va_tree_eq_surj t : { s | va_tree_eq s t }.
    Proof.
      induction t as [ x v IHv ].
      vec reif IHv as [ w Hw ].
      exists ⟨x|w⟩; now constructor.
    Qed.

    Remark va_tree_eq_wft s t : va_tree_eq s t → wft A s.
    Proof. induction 1; split; auto. Qed.

    Remark va_tree_eq_total s : wft A s → { t | va_tree_eq s t }.
    Proof.
      induction s as [ n x v IHv ]; intros (Hx & Hv)%wft_fix.
      specialize (fun p => IHv _ (Hv p)).
      vec reif IHv as [ w Hw ].
      subst n.
      exists (atree_cons x w).
      now constructor.
    Qed.

    (* This is the critical inversion lemma *)
    Lemma va_tree_eq_invl s t :
         va_tree_eq s t
       → match s with
         | @dtree_cons _ n x v => ∃ (e : n = a x) w,
                                       t = atree_cons x w↺e
                                     ∧ vec_fall2 va_tree_eq v w
         end.
    Proof. intros []; eexists eq_refl, _; simpl; eauto. Qed.

  End atree_vtree.

End vtree_atree.

Section higman_atree_af.

  Hypothesis higman_dtree : af_higman_dtree.

  Variables (k : nat) (X : Type) (a : X → nat) (R : nat → rel₂ X).

  Notation A := (λ n x, n = a x).

  Hypothesis (Hk : ∀x, a x < k)
             (HR : ∀n, n < k → af (R n)⇓(A n)).

  Let Y n := sig (A n).
  Let T n : rel₂ (Y n) := (R n)⇓(A n).

  Local Fact af_dtree_T : af (dtree_product_embed T).
  Proof.
    apply higman_dtree with (k := k).
    + intros n Hn (x & Hx).
      specialize (Hk x).
      rewrite <- Hx in Hk; tlia.
    + apply HR.
  Qed.

  Local Theorem higman_dtree_atree_af_local : af (atree_product_embed a R).
  Proof.
    generalize af_dtree_T.
    af rel morph (λ s t, dtree_atree a s = t).
    + intros s; exists (atree_dtree s).
      apply dtree_atree_dtree.
    + intros s t ? ? <- <-.
      induction 1 as [ n [ x Hx ] v t p H IH | n [ x Hx ] v [ y Hy ] w H1 H2 IH2 ]; simpl.
      * eq refl.
        constructor 1 with p.
        now vec rew.
      * eq refl.
        unfold T in H1; simpl in H1.
        constructor 2; auto.
        clear H1.
        rewrite <- Hy; simpl.
        apply vec_forall2_iff_fall2.
        now intro; vec rew.
  Qed.

End higman_atree_af.

Theorem higman_theorem_dtree_atree_af : af_higman_dtree → af_higman_atree.
Proof. exact higman_dtree_atree_af_local. Qed.

Section kruskal_atree_af.

  Hypothesis kruskal_vtree : af_kruskal_vtree.

  Variables (X : Type) (a : X → nat) (R : rel₂ X).

  Notation A := (λ n x, n = a x).

  Hypothesis (HR : af R).

  Local Fact af_vtree : af (vtree_homeo_embed R).
  Proof. apply kruskal_vtree, HR. Qed.

  Local Theorem kruskal_vtree_atree_af_local : af (atree_homeo_embed a R).
  Proof.
    generalize af_vtree.
    af rel morph (@va_tree_eq _ a).
    + intros t.
      destruct (va_tree_eq_surj t); eauto.
    + intros s t u v Hu Hv H.
      revert H u v Hu Hv.
      induction 1 as [ x n v t p H IH
                     | n x v m y w H1 H2 IH2 ]; simpl; intros c d.
      * intros Hc (e & w & -> & Hw)%va_tree_eq_invl; eq refl.
        constructor 1 with p; auto.
      * intros (e1 & v1 & -> & Hv1)%va_tree_eq_invl
               (e2 & w1 & -> & Hw1)%va_tree_eq_invl; eq refl.
        constructor 2; auto.
        clear H1 H2.
        revert v w IH2 v1 w1 Hv1 Hw1.
        generalize (a x) (a y); clear x y HR.
        induction 1 as [ | n x v m y w H1 _ IH2 | n v m y w _ IH ].
        - intros v1 w1; vec invert v1; vec invert w1; constructor.
        - intros v1 w1.
          vec invert v1 as x1 v1.
          vec invert w1 as y1 w1.
          intros []%vec_fall2_cons_inv []%vec_fall2_cons_inv.
          constructor 2; auto.
        - intros v1 w1.
          vec invert w1 as y1 w1.
          intros ? []%vec_fall2_cons_inv.
          constructor 3; auto.
  Qed.

End kruskal_atree_af.

Theorem kruskal_theorem_vtree_atree_af : af_kruskal_vtree → af_kruskal_atree.
Proof. exact kruskal_vtree_atree_af_local. Qed.


