import BFRF.LieII

/-!
# Exact BFRF Lie-equivalence integration interface

Run `python3 scripts/check_bfrf_compatibility.py` after `lake build`.
-/

noncomputable section
open BFRF.Homogeneous
open scoped Manifold ContDiff

universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {μ ν : BFRF.Bracket E} {hμ : μ.Jacobi} {hν : ν.Jacobi}
  {A : IntegratedLieGroup.{u} μ hμ} {B : IntegratedLieGroup.{u} ν hν}
  {e : BracketLie μ hμ ≃ₗ⁅ℝ⁆ BracketLie ν hν}

local instance : ENat.LEInfty (minSmoothness ℝ 3) := ⟨by simp⟩

example (f : LieGroups.LieEquivalenceIntegration
    (A.lieEquiv.trans (e.trans B.lieEquiv.symm))) : IntegratedLieEquiv A B e :=
  IntegratedLieEquiv.ofLieEquivalenceIntegration f

example [T2Space A.G] [T2Space B.G]
    (e : BracketLie μ hμ ≃ₗ⁅ℝ⁆ BracketLie ν hν) :
    Nonempty (IntegratedLieEquiv A B e) := nonempty_integratedLieEquiv e

example [T2Space A.G] [T2Space B.G]
    (e : BracketLie μ hμ ≃ₗ⁅ℝ⁆ BracketLie ν hν)
    (v : GroupLieAlgebra 𝓘(ℝ, E) A.G) :
    B.lieEquiv ((integrateLieEquiv (A := A) (B := B) e).groupEquiv.derivAtOne v) =
      e (A.lieEquiv v) := (integrateLieEquiv e).deriv_compat v

#print axioms BFRF.Homogeneous.IntegratedLieEquiv.ofLieEquivalenceIntegration
#print axioms BFRF.Homogeneous.nonempty_integratedLieEquiv
#print axioms BFRF.Homogeneous.integrateLieEquiv
