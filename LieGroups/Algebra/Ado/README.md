The Lean files in this directory are adapted from Miyahara Kō's
[Komyyy/ado](https://github.com/Komyyy/ado), commit
`232f542c83972415709682c3de25d3643ee0d840`, retrieved on 2026-10-19.
The original copyright and authorship notices are retained in every file.
The source is distributed under the Apache License 2.0, reproduced in the
repository's [LICENSE](../../../LICENSE).

The upstream proof formalizes Ado's theorem in characteristic zero, following
[Terence Tao's proof](https://terrytao.wordpress.com/2011/05/10/ados-theorem/).
It includes Casimir operators, Whitehead's lemmas, Weyl complete reducibility,
Levi decomposition, and the nilpotent and solvable representation constructions.

The adaptation rewrites imports into `LieGroups.Algebra.Ado` and ports the proof
to the repository's pinned Lean 4.34.0-rc2 and Mathlib revision. These changes are
made with AI assistance. Dependency pins are unchanged. In particular, the
characteristic-polynomial degree helper explicitly requires `Nontrivial R`.
Unused imports unavailable in the pinned Mathlib and an unused upstream
`theorem_wanted` request are omitted.

The independent PBW basis theorem is in
[PBW.lean](../PBW.lean). The project-facing Ado interface is in
[Ado.lean](../Ado.lean).
