# Contributing

Keep the advertised Howson theorem in `Challenge.lean` small and independently
auditable. The finite-core, Hall, Schreier, and Kurosh arguments belong in the
implementation modules under `MarshallHall/`, `GraphCoveringTheory/`, and
`Howson/`; `Solution.lean` should expose the checked result without adding a
second informal statement.

Before opening a pull request, run:

```text
lake build
cd docbuild && lake build HowsonIntersectionTheorem:docs
cd ..
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Do not add custom axioms or replace completed proofs with `sorry`. Keep the
checked-in Lake manifests and metadata synchronized with the source, and
preserve the Apache-2.0 license.
