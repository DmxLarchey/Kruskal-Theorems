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
several instances of Kruskal's and Higman's tree theorems, via simple surjective relational morphism.

# How to install `Kruskal-Theorems`

__WARNING:__ `Kruskal-Theorems` is not part of `coq-opam` for the moment but the
should happen on short notice. It just needs a bit of cleanup

It can be installed via `opam` since release `v1.0` is now include into [`coq-opam`](https://github.com/coq/opam).
```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-kruskal-theorems
```

Notice that to import it in a development, as with `Kruskal-AlmostFull`, one should
consistently choose between:
- the `Prop`-bounded version accessed via eg `From KruskalThmProp Require ...`;
- or the `Type`-bounded version via eg `From KruskalThmType Require ...`.

Mixing both versions is possible but hard and not recommended due 
to the total overlap of the namespaces except for the prefixes `KruskalThm{Prop,Type}`.

# What are the main results

There are several formulations of Kruskal's tree theorem available
depending on the exact representation of indexed rose trees, either 
as vectors of rose trees,... or list of rose trees which is the
simplest to present:
```coq
Inductive ltree (X : Type) : Type :=
  | in_ltree : X → list (ltree X) → ltree X
where "⟨x|l⟩ₗ" := (@in_ltree _ x l).

Inductive list_embed {X Y} (R : rel X Y) : list X → list Y → Prop :=
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

From this theorem formulated abstractly, we derive a proof of
[Vazsonyi's conjecture](https://en.wikipedia.org/wiki/Andrew_V%C3%A1zsonyi):
```coq
Theorem vazsonyi_conjecture X (R : rel₂ (ltree X)) :
      (∀ r s x l, R r s → s ∈ l → R r (ltree_cons x l))
    → (∀ x l y m, list_embed R l m → R (ltree_cons x l) (ltree_cons y m))
    → ∀f, ∃ i j, i < j < n ∧ R (f i) (f j).
```
where `R` is abstracted as any relation closed for the rules
of homeomorphic embeddings.
