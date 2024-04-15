(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import base.

Require Export statements
               veldman_vtree_upto_afs_to_kruskal_vtree_afs
               veldman_vtree_upto_afs_to_higman_dtree_afs
               kruskal_vtree_afs_to_af
               kruskal_vtree_to_ltree
               kruskal_ltree_to_vazsonyi
               kruskal_ltree_af_to_afs
               kruskal_vtree_afs_to_higman_dtree_afs
               higman_dtree_to_list
               higman_dtree_afs_to_af
               higman_dtree_to_vazsonyi_bounded
               higman_kruskal_dtree_to_atree.

(** Since afs_veldman_vtree_upto is already proved as the main theorem
    of the Kruskal-Veldman project, all the following results derive
    more or less easily from it.

    In conversions/*.v, we establish the following implications using 
    easy relational morphisms 

                           afs_veldman_vtree_upto
                                     ↓ 
                             afs_kruskal_vtree
                              ↙               ↘
                    af_kruskal_vtree         afs_higman_dtree
                      ↙         ↘                      ↘
          af_kruskal_ltree  af_kruskal_atree      af_higman_dtree
            ↙           ↘                          ↙          ↘
 vazsonyi_conjecture  afs_kruskal_ltree    af_higman_atree  vazsonyi_conjecture_bounded

   Hence establishing all the results:
    - afs_veldman_vtree_upto is recalled below as synonymous to afs_vtree_upto_embed
    - *_kruskal_* results are proved in kruskal_theorems.v
    - *_higman_* results are proved in higman_theorems.v
    - vazsonyi_* results are proved in vazsonyi_theorems.v
*)

Theorem veldman_theorem_vtree_upto : afs_veldman_vtree_upto.
Proof. exact afs_vtree_upto_embed. Qed.
