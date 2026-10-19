/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Algebra.Module.Submodule.Ker

public section

open Submodule LinearMap

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

lemma Submodule.map_le_iff_mapsTo {f : M →ₗ[R] M₂} {p q} : map f p ≤ q ↔ Set.MapsTo f p q :=
  map_le_iff_le_comap

@[simp]
lemma Submodule.map_ker {f : M →ₗ[R] M₂} : map f (ker f) = ⊥ := by
  simp [← le_ker_iff_map]
