(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Utf8.

From KruskalTrees
  Require Import tactics idx vec dtree ltree btree.

Require Import base notations le_lt_pirr
               dtree_embed ltree_embed
               statements.

Import idx_notations vec_notations dtree_notations.

Set Implicit Arguments.

#[local] Fact btree_f_equal k n v w h h' : 
     v = w → @btree_cons k n v h = @btree_cons k n w h'.
Proof. intros ->; f_equal; apply lt_pirr. Qed.

Section btree_dtree.

  (* Isomorphism between btree k and dtree (X k) for some X k *)

  Variable (k : nat).

  Local Definition dtree_bounded n :=
    if le_lt_dec k n then Empty_set else unit.

  Notation X := dtree_bounded.

  Local Definition tt' n : n < k → X n.
  Proof. 
    refine (match le_lt_dec k n as d return _ → if d then Empty_set else unit with
    | left _  => λ _, match _ : False with end
    | right _ => λ _, tt 
    end); tlia.
  Defined.

  Local Fact X_uniq n : ∀ a b : X n, a = b.
  Proof. unfold X; destruct (le_lt_dec k n); intros [] []; auto. Qed.

  Local Fixpoint btree_dtree (t : btree k) : dtree X :=
    match t with
    | btree_cons v h => ⟨tt' h|vec_map btree_dtree v⟩
    end.

  Local Fact btree_dtree_fix n v h :
       btree_dtree (@btree_cons k n v h) = ⟨tt' h|vec_map btree_dtree v⟩.
  Proof. reflexivity. Qed.

(*  Hint Resolve lt_pirr : core. *)

  Local Fact btree_dtree_inj s t : btree_dtree s = btree_dtree t → s = t.
  Proof.
    revert t; induction s as [ n v hv IH ]; intros [ m w hw ]; simpl.
    rewrite dtree_cons_inj.
    intros (e & H1 & H2); eq refl; simpl in *.
    apply btree_f_equal.
    vec ext.
    apply f_equal with (f := fun v => v⦃p⦄) in H2.
    rewrite !vec_prj_map in H2; auto.
  Qed.

  Section dtree_btree_def.

    Local Fact dtree_btree_pwc (t : dtree X) : { r | btree_dtree r = t }.
    Proof.
      induction t as [ n x v IH ].
      unfold X in x.
      case_eq (le_lt_dec k n); intros Hn E.
      + exfalso; rewrite E in x; destruct x.
      + vec reif IH as (w & Hw).
        exists (btree_cons w Hn); simpl; f_equal.
        * apply X_uniq.
        * now vec ext; vec rew.
    Qed.

    Local Definition dtree_btree t := proj1_sig (dtree_btree_pwc t).

    Local Fact btree_dtree_btree t : btree_dtree (dtree_btree t) = t.
    Proof. apply (proj2_sig (dtree_btree_pwc t)). Qed.

  End dtree_btree_def.

  Local Fact dtree_btree_dtree t : dtree_btree (btree_dtree t) = t.
  Proof. apply btree_dtree_inj; now rewrite btree_dtree_btree. Qed.

  Local Fact dtree_btree_fix n x (v : vec _ n) :
        { h : n < k | dtree_btree ⟨x|v⟩ = btree_cons (vec_map dtree_btree v) h }.
  Proof.
    unfold X in x.
    case_eq (le_lt_dec k n); intros Hn E.
    + exfalso; rewrite E in x; destruct x.
    + exists Hn.
      apply btree_dtree_inj; rewrite btree_dtree_btree, btree_dtree_fix.
      f_equal.
      * apply X_uniq.
      * vec ext; vec rew.
        now rewrite btree_dtree_btree.
  Qed.

End btree_dtree.

Section Vazsonyi_bounded.

  Variables (k : nat)
            (higman_theorem : af_higman_dtree k).

  (** We have a structural bijection !! *)

  Variables (R : btree k → btree k → Prop)
            (HR1 : ∀ r s n (h : n < k) v, R r s → s ∈ᵥ v → R r (btree_cons v h))
            (HR2 : ∀ n v m w (hn : n < k) (hm : m < k),
                         vec_forall2 R v w → R (btree_cons v hn ) (btree_cons w hm)).

  Local Fact dtree_btree_morph t₁ t₂ :
         dtree_product_embed (λ _, ⊤₂) t₁ t₂
       → R (dtree_btree t₁) (dtree_btree t₂).
  Proof.
    induction 1 as [ n x v t p H IH | n x v y w _ H IH ].
    + destruct (dtree_btree_fix x v) as (Hn & ->).
      apply HR1 with (1 := IH).
      apply vec_in_iff_prj; exists p; vec rew; auto.
    + destruct (dtree_btree_fix x v) as (H1 & ->).
      destruct (dtree_btree_fix y w) as (H2 & ->).
      apply HR2, vec_forall2_iff_fall2.
      intro; vec rew; auto.
  Qed.

  Local Theorem vazsonyi_conjecture_bounded_strong (f : nat → btree k) :
              ∃ₜ n, ∃ i j, i < j < n ∧ R (f i) (f j).
  Proof.
    apply af_good_pair.
    cut (af (dtree_product_embed (fun n (_ _ : dtree_bounded k n) => True))).
    + af rel morph (fun x y => y = dtree_btree x).
      * intros y; exists (btree_dtree y); rewrite dtree_btree_dtree; auto.
      * intros t1 t2 ? ? -> ->; apply dtree_btree_morph.
    + apply higman_theorem.
      * intro n; unfold dtree_bounded; destruct (le_lt_dec k n); tlia; intros _ [].
      * constructor; tauto.
  Qed.

End Vazsonyi_bounded.

Theorem higman_dtree_to_vazsonyi_bounded k :
        af_higman_dtree k
      → vazsonyi_conjecture_bounded k.
Proof.
  intros Hk R HR1 HR2 f.
  apply vazsonyi_conjecture_bounded_strong; eauto.
Qed.

Print vazsonyi_conjecture_bounded.

(** Notation for binary relations/predicates *)

Locate "rel₂ _".

(** Inductive definition vec X n for vectors of length n over type X,
    with notations ∅ (for empty vector in vec X 0) and ## (for cons in vec X (S _)) *)

Print vec.
Locate "∅".
Locate "##".

(** Inductive definition of membership in vectors, denoted with ∊ *)

Locate "∈ᵥ".
Print vec_in.

(** Inductive definition of the product relations over vectors of the same length *)

Print vec_forall2.

(** Inductive definition of tree of width bounded by k *)

Print btree.

(** The statement of Vazoni's conjecture for trees of bounded width,
    and a check that no assumption is used to establish it *)
Check higman_dtree_to_vazsonyi_bounded.
Print Assumptions higman_dtree_to_vazsonyi_bounded.
