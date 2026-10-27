import BFRF.Admissible

/-!
Regression checks for closed-isotropy admissibility against the actual BFRF
interfaces. The initial construction supplies its integrating group through
Lie III, and subgroup comparison assumes closedness explicitly.
-/

noncomputable section
open scoped Manifold ContDiff

namespace BFRF.Homogeneous

universe u
variable {K P : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ K] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P]
  {μ : Bracket (K × P)} {hμ : μ.Jacobi}
  (hKK : ∀ k l : K, (μ.eval (k, 0) (l, 0)).2 = 0)

/-- Admissibility alone supplies the isotropy group in the Lie-III construction. -/
theorem constructed_initial_isotropy
    (hA : IsAdmissible (integratedLieGroup (μ := μ) (hμ := hμ)) hKK) :
    ∃ KA : IntegratedIsotropySubgroup (integratedLieGroup (μ := μ) (hμ := hμ)) hKK,
      KA.Kμ = canonicalIsotropySubgroup (integratedLieGroup (μ := μ) (hμ := hμ)) hKK :=
  ⟨integratedIsotropySubgroupOfAdmissible _ hKK hA, rfl⟩

variable (A : IntegratedLieGroup.{u} μ hμ) [T2Space A.G]

/-- Ambient curve tangents are proved for the actual exponential-generated subgroup. -/
example (hA : IsAdmissible A hKK) :
    HasIsotropyTangent A hKK (canonicalIsotropySubgroup A hKK) :=
  canonicalIsotropySubgroup_hasIsotropyTangent A hKK hA

/-- The uniqueness regression includes closedness of both subgroup realizations. -/
example (H : Subgroup A.G) (hconn : IsConnected (H : Set A.G))
    (hclosed : IsClosed (H : Set A.G)) (htangent : HasIsotropyTangent A hKK H)
    (KA : IntegratedIsotropySubgroup A hKK) : H = KA.Kμ :=
  closedSubgroup_eq_of_hasIsotropyTangent A hKK H hconn hclosed htangent KA

variable {ν : Bracket (K × P)} {hν : ν.Jacobi}
  (B : IntegratedLieGroup.{u} ν hν) [T2Space B.G]
  {e : BracketLie μ hμ ≃ₗ⁅ℝ⁆ BracketLie ν hν}
  (hKKB : ∀ k l : K, (ν.eval (k, 0) (l, 0)).2 = 0)

/-- A comparison Lie equivalence produces compatibility of the actual isotropy groups. -/
example (Φ : IntegratedLieEquiv A B e)
    (KA : IntegratedIsotropySubgroup A hKK) (KB : IntegratedIsotropySubgroup B hKKB)
    (he : (BracketLie.isotropy μ hμ hKK).map e.toLieHom =
      BracketLie.isotropy ν hν hKKB) : Φ.IsotropyCompatible KA KB :=
  IntegratedLieEquiv.isotropyCompatible_of_isotropy_map A hKK Φ KA KB he

/-- Admissibility passes along the same smooth integrated equivalence. -/
example (hA : IsAdmissible A hKK) (Φ : IntegratedLieEquiv A B e)
    (he : (BracketLie.isotropy μ hμ hKK).map e.toLieHom =
      BracketLie.isotropy ν hν hKKB) : IsAdmissible B hKKB :=
  IsAdmissible.map A hKK hA Φ he

end BFRF.Homogeneous

#print axioms LieGroups.sigmaCompactSpace_of_connected_lieGroup
#print axioms LieGroups.ImmersedLieSubgroup.isEmbedding_of_isClosed
#print axioms LieGroups.subgroupTangentSet_lieSubalgebraSubgroup_of_isClosed
#print axioms BFRF.Homogeneous.canonicalIsotropySubgroup
#print axioms BFRF.Homogeneous.canonicalIsotropySubgroup_connected
#print axioms BFRF.Homogeneous.canonicalIsotropySubgroup_hasIsotropyTangent
#print axioms BFRF.Homogeneous.integratedIsotropySubgroupOfAdmissible
#print axioms BFRF.Homogeneous.canonicalIsotropySubgroup_eq_integrated
#print axioms BFRF.Homogeneous.isAdmissible_iff_nonempty_integratedIsotropySubgroup
#print axioms BFRF.Homogeneous.integratedIsotropySubgroup_eq
#print axioms BFRF.Homogeneous.closedSubgroup_eq_of_hasIsotropyTangent
#print axioms BFRF.Homogeneous.IntegratedLieEquiv.isotropyCompatible_of_isotropy_map
#print axioms BFRF.Homogeneous.IsAdmissible.map
#print axioms BFRF.Homogeneous.constructed_initial_isotropy
