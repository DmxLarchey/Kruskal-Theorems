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

Require Import base dtree_embed statements.

Import idx_notations vec_notations
       dtree_notations vtree_notations
       af_notations.

Set Implicit Arguments.

Section dtree_vtree.

  (** We build a bijection between

          dtree X   <->   sig (wft T)

     where T n (m,_ : X m) := n = m *)

  Variable (X : nat → Type).

  Let Y := sigT X.
  Let T : nat → Y → Prop := λ n s, n = projT1 s.

  Local Definition dtree_vtree (t : dtree X) : vtree Y.
  Proof.
    induction t as [ n x v f ].
    exact ⟨existT _ n x|vec_set f⟩.
  Defined.

  Local Fact dtree_vtree_fix n (x : X n) (v : vec _ n) :
       dtree_vtree ⟨x|v⟩ = ⟨existT _ n x|vec_map dtree_vtree v⟩.
  Proof. rewrite <- vec_set_map; auto. Qed.

  Local Fact dtree_vtree_inj s t : dtree_vtree s = dtree_vtree t → s = t.
  Proof.
    revert t; induction s as [ n x v IH ]; intros [ m y w ].
    rewrite !dtree_vtree_fix, dtree_cons_inj.
    intros (? & H1 & H2); eq refl; simpl in *.
    apply eq_sigT_inj in H1 as (e & H1); eq refl; subst; clear e.
    f_equal; vec ext; apply IH.
    apply f_equal with (f := fun v => v⦃p⦄) in H2.
    now rewrite !vec_prj_map in H2.
  Qed.

  Local Fact dtree_vtree_wf t : wft T (dtree_vtree t).
  Proof.
    unfold T.
    induction t.
    rewrite dtree_vtree_fix, wft_fix; simpl; split; auto.
    now intro; vec rew.
  Qed.

  Local Fact dtree_vtree_surj t' : wft T t' → { t | dtree_vtree t = t' }.
  Proof.
    unfold T.
    induction 1 as [ n (j,x) v H1 H2 IH2 ] using wft_rect.
    vec reif IH2 as (w & Hw).
    simpl in H1; subst j.
    exists ⟨x|w⟩.
    rewrite dtree_vtree_fix; f_equal.
    now vec ext; vec rew.
  Qed.

  Local Fact dtree_vtree_vec_surj n (v : vec _ n) :
         vec_fall (wft T) v → { w | vec_map dtree_vtree w = v }.
  Proof. apply vec_cond_reif, dtree_vtree_surj. Qed.

  Local Definition vtree_dtree t' Ht' := proj1_sig (dtree_vtree_surj t' Ht').

  Local Fact dtree_vtree_dtree t' Ht' : dtree_vtree (@vtree_dtree t' Ht') = t'.
  Proof. apply (proj2_sig (dtree_vtree_surj t' Ht')). Qed.

  Local Fact vtree_dtree_vtree t H : vtree_dtree (dtree_vtree t) H = t.
  Proof. apply dtree_vtree_inj; rewrite dtree_vtree_dtree; auto. Qed.

  Local Fact vtree_dtree_fix n x (w : vec (dtree X) n) H :
         vtree_dtree ⟨existT _ n x|vec_map dtree_vtree w⟩ H = ⟨x|w⟩.
  Proof. apply dtree_vtree_inj; rewrite dtree_vtree_dtree, dtree_vtree_fix; auto. Qed.

End dtree_vtree.

Section higman_afs_to_higman_af.

  Variables (higman : afs_higman_dtree) (k : nat).

  Variables (X  : nat → Type)
            (R  : ∀n, rel₂ (X n))
            (HX : ∀n, k ≤ n → X n → False)
            (HR : ∀n, n < k → af (@R n)).

  Notation Y := (sigT X).

  Let T n (y : Y) := n = projT1 y.

  Local Fact T_empty n x : k ≤ n → T n x → False.
  Proof. unfold T; intros H; destruct x as (j,x); simpl; intros; subst; revert x; apply HX; auto. Qed.

  Let R' n (u v : Y) :=
    match u, v with
    | existT _ _ x, existT _ _ y => exists e f, @R n x↺e y↺f
    end.

  Local Fact R'_afs n : n < k → afs (T n) (@R' n).
  Proof.
    intros Hn; apply afs_iff_af_sub_rel; generalize (HR Hn).
    af rel morph (fun (x : X n) (y : sig (T n)) =>
         match proj1_sig y with
           | existT _ i a => exists e, x↺e = a
         end); unfold T.
    + intros ((j,x),e); simpl in *; subst; exists x, eq_refl; auto.
    + intros x1 x2 ((i1,y1),e1) ((i2,y2),e2); simpl.
      intros (<- & ?) (<- & <-); simpl in *.
      exists eq_refl, eq_refl; simpl; subst; auto.
  Qed.

  Hint Resolve T_empty R'_afs : core.

  Local Lemma higman_afs_to_higman_af_at : af (dtree_product_embed R).
  Proof.
    cut (afs (wft T) (dtree_product_embed R')).
    2: { apply higman with k; eauto. }
    equiv with afs_iff_af_sub_rel.
    af rel morph (fun x y => vtree_dtree (proj1_sig x) (proj2_sig x) = y ).
    + intros t.
      induction t as [ n x v IH ].
      assert (Hw : forall p, ∃ₜ t (Ht : wft _ t), vtree_dtree t Ht = vec_prj v p).
      1: { intros p; destruct (IH p) as ([] & ?); eauto. }
      vec reif Hw as (w & Hw).
      idx reif Hw as (g & Hg).
      assert (Ht : wft T ⟨existT _ n x|w⟩).
      1: { unfold T; apply wft_fix; simpl; auto. }
      exists (exist _ ⟨existT _ n x|w⟩ Ht); simpl.
      apply dtree_vtree_inj; rewrite dtree_vtree_dtree, dtree_vtree_fix.
      f_equal; vec ext; vec rew.
      rewrite <- Hg, dtree_vtree_dtree; auto.
    + intros x1 x2 ? ? <- <-; revert x1 x2.
      intros (x1 & H1) (x2 & H2); simpl.
      intros H; revert H H1 H2; unfold T.
      induction 1 as [ j b v t p H1 IH1 | j b v c w H1 H2 IH2 ]; intros G1 G2; auto.
      * generalize G2.
        apply wft_fix in G2 as [ G2 G3 ].
        generalize (G3 p); intros G4.
        destruct dtree_vtree_vec_surj with (v := v) as (w & <-); auto.
        rewrite !vec_prj_map in IH1, G4.
        specialize (IH1 G1 G4).
        rewrite vtree_dtree_vtree in IH1.
        intros G5.
        destruct b as [ u b ].
        simpl in G2; subst u.
        rewrite (vtree_dtree_fix _ G5).
        constructor 1 with p; auto.
      * generalize G1 G2.
        apply wft_fix in G2 as [ G3 G4 ].
        apply wft_fix in G1 as [ G1 G2 ].
        destruct dtree_vtree_vec_surj with (1 := G2) as (v1 & <-).
        destruct dtree_vtree_vec_surj with (1 := G4) as (v2 & <-).
        intros G5 G6.
        destruct b as [ u b ]; simpl in G1; subst u.
        destruct c as [ u c ]; simpl in G3; subst u.
        rewrite !vtree_dtree_fix.
        constructor 2.
        - destruct H1 as (e & g & H1); eq refl; auto.
        - intros p.
          specialize (IH2 p).
          specialize (G2 p).
          specialize (G4 p).
          rewrite !vec_prj_map in G2, G4.
          rewrite !vec_prj_map in IH2.
          specialize (IH2 G2 G4).
          rewrite !vtree_dtree_vtree in IH2.
          trivial.
  Qed.

End higman_afs_to_higman_af.

Theorem higman_dtree_afs_to_af : afs_higman_dtree → af_higman_dtree.
Proof. intros ? ? ? ?; apply higman_afs_to_higman_af_at; auto. Qed.
