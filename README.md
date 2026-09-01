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

The next genuinely new layer is the arbitrary-factor theorem. The file
`MarshallHall/GrushkoGeneral.lean` proves the easy inequality and the lower
bound for an already separated tuple, and packages the remaining fold/Nielsen
step as `HasSeparatedReduction`. Once that theorem is supplied, the
kernel-checked bridge `rank_coprod_eq_add_of_separated_reduction` yields

```lean
Group.rank (G ∗ H) = Group.rank G + Group.rank H
```

for arbitrary finitely generated groups. The repository does not claim that
generator-reduction theorem yet.

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
- `comparator.json` records the exact Challenge/Solution correspondence.
- `formalization.yaml` records provenance, scope, and the deliberate boundary
  between the full Hall result and the free-group Grushko instance.

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

The registered Challenge/Solution surface remains the compact LERF theorem;
the stronger Hall and rank results are exported by the library root
`MarshallHall.lean`.
