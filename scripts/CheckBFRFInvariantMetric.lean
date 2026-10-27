import BFRF.IsotropyMetric
import BFRF.HomogeneousGeometricRicci

/-!
# Constructed BFRF metric and Killing realization

The first check constructs the metric and fundamental-field inputs consumed by
BFRF's homogeneous geometric Ricci calculations. The second applies both actual
downstream Ricci identification theorems to those constructed inputs. Neither
check assumes a metric, local smooth sections, field identities, or isotropy
representation.
-/

noncomputable section
open scoped Manifold ContDiff
open BFRF.Homogeneous
open DifferentialGeometry.Geometry.Curvature

universe u
variable {K P : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ K] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P]
  {μ : BFRF.Bracket (K × P)} {hμ : μ.Jacobi}
  {hKK : ∀ k l : K, (μ.eval (k, 0) (l, 0)).2 = 0}
  {A : IntegratedLieGroup.{u} μ hμ} [T2Space A.G]
  (KA : IntegratedIsotropySubgroup A hKK) (hmetric : IsMetricIsotropy μ)

example : ∃ R : RegularHomogeneousQuotientRealization A KA,
    let Q := R.toHomogeneousQuotientRealization
    ∃ g : DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, P) Q.M,
      ∃ F : (K × P) →ₗ[ℝ]
          Cₛ^∞⟮𝓘(ℝ, P); P, (TangentSpace 𝓘(ℝ, P) : Q.M → Type _)⟯,
        Q.IsInvariantMetric g ∧
        (∀ a : K × P, F a Q.o = Q.tangentEquiv a.2) ∧
        (∀ X Y : P, g.inner Q.o (Q.tangentEquiv X) (Q.tangentEquiv Y) = inner ℝ X Y) ∧
        (∀ (a : K × P) (x : Q.M) (v w : TangentSpace 𝓘(ℝ, P) x),
          DifferentialGeometry.PDE.DeTurck.lieDerivMetric g (F a) x v w = 0) ∧
        (∀ (a b : K × P) (x : Q.M),
          VectorField.mlieBracket 𝓘(ℝ, P) (F a) (F b) x = -F (μ.eval a b) x) :=
  HomogeneousQuotientRealization.exists_metric_fundamentalFields hmetric

include hmetric in
/-- The constructed metric and fields feed the actual downstream Ricci theorems.
Only reductivity is added to the geometric construction hypotheses. -/
theorem constructed_metric_ricci_identification (hred : PreservesTangent μ) :
    ∃ R : RegularHomogeneousQuotientRealization A KA,
      let Q := R.toHomogeneousQuotientRealization
      ∃ g : DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, P) Q.M,
        Q.IsInvariantMetric g ∧
        (∀ X Y : P, ricciTensor (I := 𝓘(ℝ, P)) g Q.o
          (Q.tangentEquiv X) (Q.tangentEquiv Y) = inner ℝ (ricciOp μ X) Y) ∧
        Q.tangentEquiv.toLinearEquiv.symm.conj
          (ricciSharp (I := 𝓘(ℝ, P)) g Q.o).toLinearMap = ricciOp μ := by
  obtain ⟨R, g, F, hInv, hvalue, hmetricOrigin, hKilling, hanti⟩ :=
    HomogeneousQuotientRealization.exists_metric_fundamentalFields (KA := KA) hmetric
  let Q := R.toHomogeneousQuotientRealization
  refine ⟨R, g, hInv, ?_, ?_⟩
  · exact ricciTensor_eq_ricciOp_of_killing μ g Q.o Q.tangentEquiv.toLinearEquiv F
      hvalue hmetricOrigin hKilling hanti hred
  · exact ricciSharp_eq_ricciOp_of_killing μ g Q.o Q.tangentEquiv.toLinearEquiv F
      hvalue hmetricOrigin hKilling hanti hred

#print axioms BFRF.Homogeneous.nonempty_regularHomogeneousQuotientRealization
#print axioms BFRF.Homogeneous.nonempty_homogeneousQuotientRealization
#print axioms HomogeneousQuotientRealization.originInner
#print axioms HomogeneousQuotientRealization.originInner_tangentEquiv
#print axioms HomogeneousQuotientRealization.originInner_symm
#print axioms HomogeneousQuotientRealization.originInner_pos
#print axioms HomogeneousQuotientRealization.riemannianMetric
#print axioms HomogeneousQuotientRealization.riemannianMetric_origin
#print axioms HomogeneousQuotientRealization.riemannianMetric_isInvariant
#print axioms HomogeneousQuotientRealization.isotropyConnectedSpace
#print axioms HomogeneousQuotientRealization.isotropyTangentRepresentation
#print axioms HomogeneousQuotientRealization.contMDiff_isotropyTangentRepresentation
#print axioms HomogeneousQuotientRealization.inclusion_differential_tangent_component
#print axioms HomogeneousQuotientRealization.isotropyTangentRepresentation_differential
#print axioms HomogeneousQuotientRealization.isotropyTangentRepresentation_preserves_inner
#print axioms HomogeneousQuotientRealization.originInner_isIsotropyInvariant
#print axioms HomogeneousQuotientRealization.exists_metric_fundamentalFields
#print axioms constructed_metric_ricci_identification
