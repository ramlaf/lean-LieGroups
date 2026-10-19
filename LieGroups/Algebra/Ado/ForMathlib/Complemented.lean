/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Order.Disjoint

public section Complemented

variable {α} [Lattice α] [BoundedOrder α]

lemma IsCompl.isComplemented {a b : α} (h : IsCompl a b) : IsComplemented a :=
  ⟨b, h⟩

alias IsCompl.isComplemented_left := IsCompl.isComplemented

lemma IsCompl.isComplemented_right {a b : α} (h : IsCompl a b) : IsComplemented b :=
  h.symm.isComplemented
