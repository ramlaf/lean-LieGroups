import BFRF.GlobalCorrespondence

/-!
Checks the completed existence endpoint against the actual Ricci-flow solution
interface, with no supplied infinitesimal fields or target realizations.
-/

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace BFRF.Homogeneous

universe u
variable {K P : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ K] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P]
  {μ : Bracket (K × P)} {hμ : μ.Jacobi}
  {hKK : ∀ k l : K, (μ.eval (k, 0) (l, 0)).2 = 0}

/-- Closedness supplies the complete initial geometric realization. -/
example (hmetric : IsMetricIsotropy μ)
    (hA : IsAdmissible (integratedLieGroup (μ := μ) (hμ := hμ)) hKK) :
    Nonempty (InitialHomogeneousRealization μ hμ hKK) :=
  nonempty_initialHomogeneousRealization μ hμ hKK hmetric hA

variable {A : IntegratedLieGroup.{u} μ hμ} [T2Space A.G]
  {KA : IntegratedIsotropySubgroup A hKK}
  (QA : RegularHomogeneousQuotientRealization A KA)

/-- The actual solution interface supplies the correspondence without an `F`,
Killing identities, bracket identities, or global target data among its inputs. -/
example (hred : PreservesTangent μ) (hmetric : IsMetricIsotropy μ)
    {D : RealTimeInterval} (S : SolutionOn (I := 𝓘(ℝ, P)) (M := QA.M) D)
    (hEq : MetricVariationEquationOn S)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hinitial : ∀ X Y : P,
      (S.family.metric t₀).inner QA.toHomogeneousQuotientRealization.o
        (QA.tangentEquiv X) (QA.tangentEquiv Y) = inner ℝ X Y)
    (hInv : ∀ t ∈ Ioo a b,
      QA.toHomogeneousQuotientRealization.IsInvariantMetric (S.family.metric t))
    (hR : ContinuousOn (fun t => basepointRicciOp (S.family.metric t)
      QA.toHomogeneousQuotientRealization.o QA.tangentEquiv.toLinearEquiv) (Ioo a b)) :
    Nonempty (GlobalBFRFCorrespondence QA S.family.metric a b t₀) :=
  homogeneous_global_bf_rf_of_invariant_ricci_flow hred hmetric QA S hEq
    ht₀ hreg hinitial hInv hR

/-- The global comparison really exists, satisfies pullback, and retains the
normalized tangent change of frame on its actual quotient manifolds. -/
theorem constructed_global_comparison
    {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, P) QA.M} {a b t₀ : ℝ}
    (C : GlobalBFRFCorrespondence QA g a b t₀) (t : Ioo a b) :
    ∃ R : ConstructedGlobalBFRealization μ hμ hKK C.hp
        QA.toHomogeneousQuotientRealization a b,
      Diffeomorph.pullbackMetric (R.targetMetric t) (R.φ t) = g t.1 ∧
      R.φ t QA.toHomogeneousQuotientRealization.o = (R.QB t).o ∧
      (∀ X : P,
        mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) (R.φ t : QA.M → (R.QB t).M)
          QA.toHomogeneousQuotientRealization.o (QA.tangentEquiv X) =
          (R.QB t).tangentEquiv (C.hp t.1 X)) :=
  ⟨C.realization, C.pullback_metric_eq t, C.φ_origin t, C.φ_mfderiv_origin t⟩

end BFRF.Homogeneous

#check BFRF.Homogeneous.lauret_global_bf_rf_of_admissible_bracket
#print axioms BFRF.Homogeneous.nonempty_initialHomogeneousRealization
#print axioms BFRF.Homogeneous.InitialHomogeneousRealization.eq_metric_of_invariant_normalized
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.metric_isotropy
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.frame_ode_right
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.realization
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.φ_origin
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.φ_equivariant
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.φ_mfderiv_origin
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.pullback_metric_eq
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.φ_apply
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.targetMetric_eq
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.comparison_eq
#print axioms BFRF.Homogeneous.GlobalBFRFCorrespondence.contMDiff_comparison
#print axioms BFRF.Homogeneous.homogeneous_bf_rf_equivalence_on_constructed_quotient
#print axioms BFRF.Homogeneous.globalBFRFCorrespondence_of_bracketFlow
#print axioms BFRF.Homogeneous.homogeneous_global_bf_rf_of_invariant_basepoint_ricci_flow
#print axioms BFRF.Homogeneous.homogeneous_global_bf_rf_of_invariant_ricci_flow
#print axioms BFRF.Homogeneous.lauret_global_bf_rf_of_admissible_bracket
#print axioms BFRF.Homogeneous.constructed_global_comparison
