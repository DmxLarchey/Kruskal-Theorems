(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From KruskalTrees
  Require Import list_utils idx vec dtree vtree.

Require Import base.

Require Export statements.

(** Since afs_veldman_vtree_upto is already proved as the main theorem
    of the Kruskal-Veldman project, all the following results derive
    more or less easily from it.

    In conversions/*.v, we establish the following implications using 
    easy relational morphisms 

                           afs_veldman_vtree_upto
                                   ↓ 
                             afs_kruskal_vtree
                              ↙             ↘
                    af_kruskal_vtree      afs_higman_dtree
                           ↓                      ↘
                    af_kruskal_ltree           af_higman_dtree
                        ↙      ↘                      ↘
       vazsonyi_conjecture   afs_kruskal_ltree     vazsonyi_conjecture_bounded

   Hence establishing all the results. *)

Require Export   veldman_vtree_upto_afs_to_kruskal_vtree_afs
                 kruskal_vtree_afs_to_af
                 kruskal_vtree_to_ltree
                 kruskal_ltree_to_vazsonyi
                 kruskal_ltree_af_to_afs
                 kruskal_vtree_afs_to_higman_dtree_afs
                 higman_dtree_afs_to_af
                 higman_dtree_to_vazsonyi_bounded.

(*
Check higman_dtree_to_list.
Check higman_dtree_afs_to_af.
Check higman_dtree_to_vazsonyi_bounded.
Check kruskal_vtree_to_ltree.
Check kruskal_ltree_af_to_afs.
Check kruskal_ltree_afs_to_af.
Check kruskal_vtree_af_to_afs.
Check kruskal_vtree_afs_to_af.
Check kruskal_vtree_afs_to_higman_dtree_afs.
Check kruskal_vtree_upto_afs_to_higman_dtree_afs.
Check kruskal_ltree_to_vazsonyi.
*)

