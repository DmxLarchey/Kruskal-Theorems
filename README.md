```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# What is this library?

The library is build on top of [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull)
and derives, from the involved proof of the result in [`Kruskal-Veldman`](https://github.com/DmxLarchey/Kruskal-Veldman), 
several instances of Kruskal's and Higman's tree theorems. 

The proofs of those derived theorems are much simpler, ie. all the complexity is hidden in the 
[`Kruskal-Veldman`](https://github.com/DmxLarchey/Kruskal-Veldman) main result.
They proceed via simple surjective relational morphism, or, as a degenerate case of morphism, 
simple inclusion between relations.

# How to install `Kruskal-Theorems`

It can be installed via `opam` since release `v1.0` which is now included 
in [`coq-opam`](https://github.com/coq/opam).
```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-kruskal-theorems
```

Notice that to import it in a development, as with [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull), one should
consistently choose between:
- the `Prop`-bounded version accessed via eg `From KruskalThmProp Require ...`;
- or the `Type`-bounded version via eg `From KruskalThmType Require ...`.

Mixing both versions is possible but hard and not recommended due 
to the total overlap of the namespaces except for the prefixes `KruskalThm{Prop,Type}`.

# What are the main results

There are several formulations of [_Kruskal's tree theorem_](https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem#:~:text=In%20mathematics%2C%20Kruskal's%20tree%20theorem,quasi%2Dordered%20under%20homeomorphic%20embedding.)
available depending on the exact representation of indexed rose trees, either 
as vectors of rose trees,... or list of rose trees which is the
simplest to present:
```coq
Inductive ltree (X : Type) : Type :=
  | in_ltree : X → list (ltree X) → ltree X
where "⟨x|l⟩ₗ" := (@in_ltree _ x l).

Inductive list_embed {X Y} (R : X → Y → Prop) : list X → list Y → Prop :=
  | list_embed_nil :           [] ≤ₗ []
  | list_embed_head x l y m :  R x y → l ≤ₗ m → x::l ≤ₗ y::m
  | list_embed_skip l y m :    l ≤ₗ m → l ≤ₗ y::m
where "l ≤ₗ m" := (list_embed R l m).

Inductive ltree_homeo_embed {X} (R : rel₂ X) : ltree X → ltree X → Prop :=
  | homeo_embed_subt s t x l : t ∈ l → s ≤ₕ t → s ≤ₕ ⟨x|l⟩ₗ
  | homeo_embed_root x l y m : R x y → list_embed ≤ₕ l m → ⟨x|l⟩ₗ ≤ₕ ⟨y|m⟩ₗ
where "s ≤ₕ t" := (ltree_homeo_embed R s t).

Theorem af_ltree_homeo_embed X (R : rel₂ X) : af R → af (ltree_homeo_embed R).
```
and herein proved in [`kruskal_theorems.v`](theories/kruskal_theorems.v) 

From this theorem formulated abstractly, we derive a proof of
[_Vazsonyi's conjecture_](https://en.wikipedia.org/wiki/Andrew_V%C3%A1zsonyi)
(which turned out to be a theorem) and which is proved here in [`vazsonyi_theorems`](theories/vazsonyi_theorems.v):
```coq
Theorem vazsonyi_theorem X (R : rel₂ (ltree X)) :
      (∀ s t x l, t ∈ l → R s t → R r ⟨x|l⟩ₗ)
    → (∀ x l y m, list_embed R l m → R ⟨x|l⟩ₗ ⟨y|m⟩ₗ)
    → ∀f : nat → ltree X, ∃ i j, i < j < n ∧ R (f i) (f j).
```
where `R` is abstracted as any relation closed for the rules
of homeomorphic embeddings.
