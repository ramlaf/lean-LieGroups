/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Data.Set.Operations

public section

variable {α β : Type*}

namespace Set

lemma MapsTo.imp {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t) : ∀ x ∈ s, f x ∈ t :=
  h

end Set
