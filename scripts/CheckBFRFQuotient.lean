import BFRF.ClosedSubgroupQuotient

/-!
# Actual BFRF quotient construction and axiom audit

Run `python3 scripts/check_bfrf_compatibility.py` after `lake build`.
The quotient interface is obtained from the ordinary closed isotropy record;
no quotient charts, local sections, or descent property are assumed.
-/

noncomputable section
open BFRF.Homogeneous
open scoped Manifold ContDiff

universe u
variable {K P : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ K] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P]
  {μ : BFRF.Bracket (K × P)} {hμ : μ.Jacobi}
  {hKK : ∀ k l : K, (μ.eval (k, 0) (l, 0)).2 = 0}
  {A : IntegratedLieGroup.{u} μ hμ} [T2Space A.G]

example (KA : IntegratedIsotropySubgroup A hKK) :
    Nonempty (HomogeneousQuotientRealization A KA) :=
  nonempty_homogeneousQuotientRealization KA

#print axioms BFRF.Homogeneous.nonempty_homogeneousQuotientRealization
