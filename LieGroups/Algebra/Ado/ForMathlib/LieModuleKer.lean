/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Algebra.Torsor.Defs
public import LieGroups.Algebra.Ado.ForMathlib.LieModuleProd

public section

open LieHom

variable {R L M N : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [LieRingModule L M] [LieRingModule L N]
variable [LieModule R L M] [LieModule R L N]


@[simp]
lemma Prod.lieModule_ker_eq :
    LieModule.ker R L (M × N) = LieModule.ker R L M ⊓ LieModule.ker R L N := by
  ext x; simp [forall_and]

@[simp]
lemma LieSubalgebra.ker_eq (L' : LieSubalgebra R L) :
    LieModule.ker R L' M = comap L'.incl (LieModule.ker R L M) := by
  ext x; simp

@[simp]
lemma LieIdeal.ker_eq (I : LieIdeal R L) :
    LieModule.ker R I M = comap I.incl (LieModule.ker R L M) := by
  ext x; simp

variable (R) in
lemma LieModule.isTrivial_iff_ker : IsTrivial L M ↔ LieModule.ker R L M = ⊤ := by
  simp_rw [eq_top_iff, SetLike.le_def, LieSubmodule.mem_top, true_implies, LieModule.mem_ker]
  exact ⟨fun _ ↦ IsTrivial.trivial, IsTrivial.mk⟩
