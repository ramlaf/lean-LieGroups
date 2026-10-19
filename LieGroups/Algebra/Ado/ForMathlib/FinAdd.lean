/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō

Adapted for lean-LieGroups on 2026-10-19 from Komyyy/ado,
commit 232f542c83972415709682c3de25d3643ee0d840.
Changes: local import paths and compatibility with pinned Mathlib/Lean.
-/
module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.ApplyFun

public section

open Function

namespace Fin

@[simp]
lemma castAdd_ne_natAdd {m n} (i : Fin m) (j : Fin n) : castAdd n i ≠ natAdd m j := by
  apply_fun addCases (fun _ ↦ false) (fun _ ↦ true); simp

@[simp]
lemma natAdd_ne_castAdd {m n} (i : Fin n) (j : Fin m) : natAdd m i ≠ castAdd n j :=
  castAdd_ne_natAdd j i |>.symm

@[simp]
lemma update_append_castAdd {α m n} (x : Fin m → α) (y : Fin n → α) (i : Fin m) (a : α) :
    update (append x y) (castAdd n i) a = append (update x i a) y := by
  ext j; cases j using addCases <;> simp [update_apply]

@[simp]
lemma update_append_natAdd {α m n} (x : Fin m → α) (y : Fin n → α) (i : Fin n) (a : α) :
    update (append x y) (natAdd m i) a = append x (update y i a) := by
  ext j; cases j using addCases <;> simp [update_apply]

@[elab_as_elim]
def appendCases {α m n} {motive : (Fin (m + n) → α) → Sort*}
    (append : (f g : _) → motive (Fin.append f g))
    (x : Fin (m + n) → α) : motive x :=
  _root_.cast (by rw [append_castAdd_natAdd])
    (append (fun i ↦ x (castAdd n i)) (fun i ↦ x (natAdd m i)))

end Fin
