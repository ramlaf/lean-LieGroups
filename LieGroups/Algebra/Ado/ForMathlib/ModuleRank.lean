/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open Module

namespace Submodule

@[congr]
lemma finrank_congr {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} (h : p = q) : finrank R p = finrank R q :=
  (LinearEquiv.ofEq p q h).finrank_eq

lemma finrank_lt_iff {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {s : Submodule K V} : finrank K s < finrank K V ↔ s < ⊤ where
  mp := lt_top_of_finrank_lt_finrank
  mpr := finrank_lt ∘ ne_top_of_lt

end Submodule
