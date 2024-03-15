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

Require Export higman_dtree_to_list
                 higman_dtree_afs_to_af
                 kruskal_vtree_to_ltree
                 kruskal_ltree_afs_to_af
                 kruskal_ltree_af_to_afs
                 kruskal_vtree_af_to_afs
                 kruskal_vtree_afs_to_af
                 kruskal_vtree_afs_to_higman_dtree_afs
                 kruskal_vtree_upto_afs_to_higman_dtree_afs
                 higman_dtree_to_vazsonyi_bounded
                 kruskal_ltree_to_vazsonyi.


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

