/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Algebra.Lie.Basic

@[expose] public section

variable {R L : Type*}

namespace PUnit

instance : Bracket L PUnit where
  bracket _ _ := unit

-- Lie 代数でも Lie 加群でも変わらないので `lie_module_bracket` とは書かない
@[simp]
lemma bracket_eq (x : L) (m : PUnit) : ⁅x, m⁆ = unit :=
  rfl

instance [LieRing L] : LieRingModule L PUnit where
  add_lie _ _ _ := by subsingleton
  lie_add _ _ _ := by subsingleton
  leibniz_lie _ _ _ := by subsingleton

instance [CommRing R] [LieRing L] [LieAlgebra R L] : LieModule R L PUnit where
  smul_lie _ _ _ := by subsingleton
  lie_smul _ _ _ := by subsingleton

end PUnit
