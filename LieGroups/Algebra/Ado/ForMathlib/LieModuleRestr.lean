/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Algebra.Lie.Submodule

public section

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

namespace LieSubmodule

@[simp]
lemma restr_top (L' : LieSubalgebra R L) : restr (⊤ : LieSubmodule R L M) L' = ⊤ := by
  simp [← toSubmodule_inj]

@[simp]
lemma restr_bot (L' : LieSubalgebra R L) : restr (⊥ : LieSubmodule R L M) L' = ⊥ := by
  simp [← toSubmodule_inj]

end LieSubmodule
