# Contributing

Keep the advertised theorem in `Challenge.lean` small and independently
auditable. The finite suffix-state construction lives in
`MarshallHall/FiniteCore.lean` and `MarshallHall/Separation.lean`; it is
exposed from `Solution.lean`.

Before opening a pull request, run:

```text
lake build
cd docbuild && lake build MarshallHall:docs
cd ..
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Do not add custom axioms or replace completed proofs with `sorry`. Keep the
checked-in Lake manifests and metadata synchronized with the source, and
preserve the Apache-2.0 license.
