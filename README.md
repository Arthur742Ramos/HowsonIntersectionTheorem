# Marshall Hall's theorem through finite cores

This repository formalizes Marshall Hall's finite-index free-factor theorem
for finitely generated subgroups of finite-rank free groups. Its main library
theorem is:

```lean
theorem MarshallHall.marshallHall
    {α : Type*} [Finite α]
    (H : Subgroup (FreeGroup α)) [Group.FG H] :
    Nonempty (MarshallHallWitness H)
```

The witness contains a subgroup `K`, the inclusion `H ≤ K`, the finite-index
condition `K.index ≠ 0`, and an explicit equivalence
`H ∗ complement ≃* K` whose left coproduct injection is the actual subgroup
inclusion. Thus the formal statement records the free-factor conclusion, not
merely an abstract isomorphism with some unspecified subgroup.

The same development proves the subgroup-separability (LERF) consequence:

```lean
theorem freeGroup_subgroup_separable
    {α : Type*} [Finite α]
    (H : Subgroup (FreeGroup α)) [Group.FG H]
    (g : FreeGroup α) (hg : g ∉ H) :
    ∃ K : Subgroup (FreeGroup α),
      H ≤ K ∧ K.index ≠ 0 ∧ g ∉ K
```

The proof is a finite-state version of the covering-graph argument. A finite
generating set for `H` is extracted from `Group.FG H`. The implementation
enumerates every suffix state of those generators and of `g`, viewed in the
left-coset quotient by `H`. Each generator gives a partial permutation on this
finite core. `Equiv.extendSubtype` completes that partial permutation to a
permutation of the finite state set. The orbit of the base state is the
connected core, and a geodesic spanning tree supplies a free basis. The
subgroup generators retract to the basis elements supported in the finite
core; this proves that `H` is a free factor of the stabilizer. Including the
suffix states of a separating word gives the LERF theorem as well.

The public Challenge is intentionally tiny and Mathlib-only. The checked
finite-core construction is in the `MarshallHall/` modules.

## Additional rank result

The repository also proves the binary free-group instance of
Grushko--Neumann rank additivity:

```lean
theorem MarshallHall.rank_binaryFreeProduct
    {α β : Type*} [Fintype α] [Fintype β] :
    Group.rank (FreeGroup α ∗ FreeGroup β) =
      Fintype.card α + Fintype.card β
```

This identifies the free product with the free group on the disjoint union
of the bases and proves the lower bound through abelianization. The library
also contains the finite indexed analogue:

```lean
theorem MarshallHall.GeneralGrushko.rank_coprodI_freeGroup
    {ι : Type*} [Fintype ι] (α : ι → Type*)
    [∀ i, Fintype (α i)] :
    Group.rank (Monoid.CoprodI (fun i => FreeGroup (α i))) =
      ∑ i, Fintype.card (α i)
```

The next layer is now complete: for arbitrary finitely generated groups, the
finite labelled-graph reduction proves the full binary theorem:

```lean
theorem MarshallHall.rank_freeProduct_eq_add
    {G H : Type u} [Group G] [Group H]
    [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H
```

The proof starts from a finite subdivided rose for a generating tuple. A
minimal null path contains a null monochromatic run. Safe folds reduce the
vertex set directly; in the edge-reuse case, a source-unfold creates a safe
fold, and an explicit monochromatic-vertex contraction removes the remaining
extra vertex. Both branches preserve the marking, generation, connectivity,
reverse-freeness, and Euler bound, so strong induction closes the separated-
generator theorem and the rank lower bound.

`MarshallHall/GrushkoGeneral.lean` contains the factorwise rank bookkeeping
and the kernel-checked bridge

```lean
Group.rank (G ∗ H) = Group.rank G + Group.rank H
```

for arbitrary finitely generated groups, while `MarshallHall/GrushkoFull.lean`
supplies the complete reduction. The source-unfold and marking-preserving
contraction are split into `GrushkoUnfold.lean`, `GrushkoRemove.lean`, and
`GrushkoUnsafe.lean` so the strict decrease is independently auditable.

## References

- M. Hall, Jr., [Subgroups of finite index in free groups](https://doi.org/10.4153/CJM-1949-017-2), *Canadian Journal of Mathematics* 1 (1949), 187--190.
- J. R. Stallings, [Topology of finite graphs](https://doi.org/10.1007/BF02095993), *Inventiones Mathematicae* 71(3) (1983), 551--565.
- I. Kapovich and A. Myasnikov, [Stallings foldings and subgroups of free groups](https://doi.org/10.1006/jabr.2001.9033), *Journal of Algebra* 248(2) (2002), 608--668.
- B. H. Neumann, [On the Number of Generators of a Free Product](https://doi.org/10.1112/jlms/s1-18.1.12), *Journal of the London Mathematical Society* 18(1) (1943), 12--20.

## Repository map

- `Challenge.lean` is the closure-safe Palomar statement surface.
- `Solution.lean` connects that surface to the checked implementation.
- `MarshallHall/PartialAction.lean` defines the left-coset action and finite
  partial-action extension lemmas.
- `MarshallHall/FiniteCore.lean` enumerates reduced-word suffix states and
  proves their finite-core membership properties.
- `MarshallHall/Separation.lean` completes the finite actions and proves the
  LERF theorem.
- `MarshallHall/GraphBasis.lean` builds the labelled Schreier graph and its
  spanning-tree free basis.
- `MarshallHall/Completion.lean` defines the good finite core and its
  connected/tree completion.
- `MarshallHall/CoreSupport.lean` proves the basis retraction and support
  lemmas used by the free-factor argument.
- `MarshallHall/FreeFactor.lean` defines inclusion-compatible free-factor
  witnesses and the basis-support criterion.
- `MarshallHall/Hall.lean` proves `MarshallHall.marshallHall` by combining
  the finite-state action with the finite-core spanning-tree argument.
- `MarshallHall/Grushko.lean` proves the binary free-group rank formula.
- `MarshallHall/GrushkoGeneral.lean` proves finite-family free-group rank,
  the factorwise bounds for arbitrary factors, and the exact bridge from
  separated generators to the full Grushko equality.
- `MarshallHall/GrushkoReduction.lean` supplies the checked binary normal-form
  bridge, alternating-word identity criterion, and Nielsen-minimality calculus
  used by the global fold/reduction theorem.
- `MarshallHall/GrushkoFold.lean` adds the next fold-proof invariant: an
  explicit `List.splitBy` decomposition into maximal monochromatic runs, with
  a certified proof that a nonempty null-labelled word contains a null
  monochromatic run.
- `MarshallHall/GrushkoGraph.lean` gives the graph-facing path semantics: an
  oriented-edge labelling reads composition as multiplication and reversal as
  inversion, and path-level Nielsen moves are proved to induce the actual
  algebraic Nielsen moves on the tuple of labels.
- `MarshallHall/GrushkoRose.lean` constructs the finite subdivided rose for a
  tuple of reduced factor words.  Its marked loops read exactly the tuple,
  the vertex type is finite, and the underlying symmetrized graph is proved
  weakly connected.  This is the certified initial graph for the fold
  induction.
- `MarshallHall/GrushkoInvariant.lean` proves the exact Euler-characteristic
  bound for the initial rose and shows that a safe fold preserves the bound
  while strictly reducing the finite vertex set.
- `MarshallHall/GrushkoUnfold.lean` formalizes the finite source-unfold move
  used in the unsafe edge-reuse case.  It constructs the duplicated edge and
  compatible reversal/labels, proves the exact vertex and oriented-edge
  cardinal changes, preserves the Euler bound, and proves that the old copy
  is monochromatic.
- `MarshallHall/GrushkoRemove.lean` formalizes the marking-preserving
  contraction of a monochromatic vertex, including path-read transport,
  connectivity, reverse-freeness, and the exact Euler decrease.
- `MarshallHall/GrushkoUnsafe.lean` connects source-unfolding, safe folding,
  and monochromatic-vertex contraction into one certified reduction package.
- `MarshallHall/GrushkoReductionChain.lean` packages the global strong
  induction interface from graph reductions to separated generators.
- `MarshallHall/GrushkoFull.lean` reroots minimal null paths, applies the
  complete reduction at every nonterminal stage, and proves the arbitrary-
  factor Grushko--Neumann theorem by strong induction.
- `comparator.json` records the exact Challenge/Solution correspondence.
- `formalization.yaml` records provenance, scope, and the relationship between
  the Hall, LERF, and Grushko results.

## Verification

The project is pinned to Lean 4.32.0 and Mathlib v4.32.0.

```text
lake build
lake env lean --src-deps Challenge.lean
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The Challenge contains one deliberate proof hole. The Solution and the
implementation library contain no proof holes or custom axioms.

The current Palomar Challenge/Solution surface selects the arbitrary-factor
Grushko--Neumann rank theorem. The Hall free-factor and LERF results remain
proved and exported by the library root `MarshallHall.lean`.
