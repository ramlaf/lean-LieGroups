/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.LinearAlgebra.Charpoly.Basic

public section

variable {R M : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Polynomial Module

namespace LinearMap

lemma charpoly_degree [StrongRankCondition R] [Nontrivial R] :
    degree (charpoly f) = finrank R M := by
  rw [charpoly, Matrix.charpoly_degree_eq_dim, finrank_eq_card_chooseBasisIndex]

end LinearMap
