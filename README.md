# Finite-core separation for free groups

This repository formalizes the subgroup-separability (LERF) consequence of
Marshall Hall's theorem:

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
finite core. `Equiv.extendSubtype` completes that partial permutation, and the
free group acts on the resulting finite state set. The stabilizer of the base
state contains `H`, has finite index, and does not contain `g`.

The public Challenge is intentionally tiny and Mathlib-only. The checked
finite-core construction is in `MarshallHall/FiniteCore.lean` and
`MarshallHall/Separation.lean`.

## Scope

The headline theorem is the LERF consequence of the full Marshall Hall
theorem. The stronger statement that every finitely generated subgroup is a
free factor of a finite-index subgroup is the next layer: it requires retaining
the core as an embedded graph and extending a core spanning tree to a spanning
tree of the completed cover. This repository records that boundary explicitly
instead of presenting the weaker separation theorem as the full free-factor
statement.

## Repository map

- `Challenge.lean` is the closure-safe Palomar statement surface.
- `Solution.lean` connects that surface to the checked implementation.
- `MarshallHall/PartialAction.lean` defines the left-coset action and finite
  partial-action extension lemmas.
- `MarshallHall/FiniteCore.lean` enumerates reduced-word suffix states and
  proves their finite-core membership properties.
- `MarshallHall/Separation.lean` completes the finite actions and proves the
  LERF theorem.
- `comparator.json` records the exact Challenge/Solution correspondence.
- `formalization.yaml` records provenance, scope, and the deliberate boundary
  between the LERF consequence and the stronger free-factor theorem.

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

When this snapshot is ready for registry review, submit its immutable commit
through the [Palomar submission form](https://submit.palomar-registry.org/).
