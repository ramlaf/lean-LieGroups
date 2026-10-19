/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Algebra.Lie.Ideal

public section

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

lemma coe_bracket (I : LieIdeal R L) (x y : I) : (↑⁅x, y⁆ : L) = ⁅(↑x : L), (↑y : L)⁆ := by
  simp

end LieIdeal
