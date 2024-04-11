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
  Require Import tactics idx vec dtree vtree.

Require Import base
               dtree_embed vtree_embed
               statements.

Import idx_notations vec_notations
       vtree_notations dtree_notations
       af_notations.

Set Implicit Arguments.

Section kruskal_afs_to_higman_afs.

  Hypothesis kruskal : afs_kruskal_vtree.

  Variables (k : nat) (U : Type)
            (X : nat → rel₁ U)
            (R : nat → rel₂ U)
            (Hk  : ∀ n x, k ≤ n → X n x → False)
            (HXR : ∀ n, n < k → afs (X n) (R n)).

  (* We consider uniform vtrees decorated with {1,...,k} * U
     and of those (p,x), only those which satisfy X p x *)

  Let V := (idx k * U)%type.
  Let Y : V → Prop := λ '(p,x), X (idx2nat p) x.
  Let T : V → V → Prop := λ '(p,x) '(q,y), p = q ∧ R (idx2nat p) x y.
  Let W : nat → V → Prop := λ _, Y.

  Local Fact af_R (p : idx k) : af (R (idx2nat p))⇓(X (idx2nat p)).
  Proof. apply afs_iff_af_sub_rel; apply HXR, idx2nat_lt. Qed.

  (* Using finite dependent sum, T is afs over Y *)

  Local Fact afs_YT : afs Y T.
  Proof.
    generalize (af_dep_sum _ _ af_R).
    intros H; apply afs_iff_af_sub_rel; revert H.
    af rel morph (fun x y =>
      match x with
        existT _ p (exist _ x Hx) => proj1_sig y = (p,x)
      end).
    + intros ((p,x) & Hx).
      exists (existT _ p (exist _ x Hx)); auto.
    + intros (p1 & x1 & ?) (p2 & x2 & ?) (y1 & ?) (y2 & ?); simpl.
      intros -> -> (e & H); eq refl; simpl; auto.
  Qed.

  (** Homeomorphic embedding T is afs over wf Y trees decorated with
         idk k * U such that
             Y (p,x) := X p x
             T (p,x) (q,y) := p = q /\ R p x y
    *)

  Local Fact afs_embed_T1 : afs (wft W) (vtree_homeo_embed T).
  Proof. apply kruskal, afs_YT. Qed.

  (* We consider uniform vtrees such that at node (p,x),
     not only X p x holds but holds its arity must be p *)

  Let K : ∀n, V → vec (vtree V) n → Prop :=
    λ n '(p,x) _, n = idx2nat p ∧ X n x.

  Local Fact K_inc_W : ∀ n x v, @K n x v → W n x.
  Proof. intros ? [] _ (-> & ?); simpl; auto. Qed.

  Local Fact dtree_fall_K_inc_wft_W : dtree_fall K ⊆₁ wft W.
  Proof. apply dtree_fall_mono, K_inc_W. Qed.

  (** Homeomorphic embedding of T is afs over wf K dtrees decorated with
         pos k * U such that

           K n (p,x) v   := n = p /\ X n x
           T (p,x) (q,y) := p = q /\ R p x y

      Over these, the homeomorphic embedding and the product (Higman)
      embedding match *)

  Hint Resolve dtree_fall_K_inc_wft_W : core.

  Local Fact afs_embed_T2 : afs (dtree_fall K) (vtree_homeo_embed T).
  Proof. apply afs_mono with (3 := afs_embed_T1); auto. Qed.

  (* f forgets part of the decoration ie (_,x) => x *)

  Local Definition f : vtree V → vtree U.
  Proof.
    induction 1 as [ n (_,x) v f ].
    exact ⟨x|vec_set f⟩.
  Defined.

  Local Fact Hf n p x (v : vec _ n) : f ⟨(p,x)|v⟩ = ⟨x|vec_map f v⟩.
  Proof. rewrite <- vec_set_map; auto. Qed.

  Local Lemma kruskal_afs_to_higman_afs_at : afs (wft X) (dtree_product_embed R).
  Proof.
    generalize afs_embed_T2; equiv with afs_iff_af_sub_rel.
    af rel morph (fun x y => f (proj1_sig x) = proj1_sig y).
    + intros (t & Ht); simpl; revert t Ht.
      induction 1 as [ n x v Hx Hv IHv ] using wft_rect.
      vec reif IHv as (w & Hw).
      assert (n < k) as Hn.
      1: { destruct (le_lt_dec k n) as [ H | ]; auto.
           exfalso; revert H Hx; apply Hk. }
      set (t := ⟨(nat2idx Hn,x)|vec_set (fun p => proj1_sig w⦃p⦄)⟩).
      assert (Ht : dtree_fall K t).
      1: { unfold t, K; rewrite dtree_fall_fix; simpl; split.
           + rewrite idx2nat2idx; auto.
           + intros p; vec rew.
             apply (proj2_sig w⦃p⦄). }
      exists (exist _ t Ht); simpl; f_equal.
      now vec ext; vec rew.
    + intros (x1 & H1) (x2 & H2) (y1 & H3) (y2 & H4); simpl.
      intros <- <- H5; revert H5 H1 H2; clear H3 H4.
      induction 1 as [ t n [q u] v p H1 IH1 | n [q x] v m [r y] w (H0 & H1) H2 IH2 ].
      * intros ? [[]]; rewrite Hf; simpl.
        constructor 1 with p; vec rew; auto.
      * intros ((H3 & H4) & H5) ((H6 & H7) & H8).
        rewrite !Hf; subst r; simpl.
        rewrite <- H6 in H3; subst m.
        constructor 2; subst; auto.
        apply vec_embed_fall2_eq in IH2.
        intro; vec rew; auto.
  Qed.

End kruskal_afs_to_higman_afs.

Theorem kruskal_vtree_afs_to_higman_dtree_afs : afs_kruskal_vtree → afs_higman_dtree.
Proof. intros ? ? ? ? ? ?; apply kruskal_afs_to_higman_afs_at; auto. Qed.
