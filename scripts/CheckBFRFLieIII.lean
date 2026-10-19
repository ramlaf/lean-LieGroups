import BFRF.LieIII

/-!
# Constructed BFRF integration records

The unrestricted constructor supplies the actual downstream record and retains
Hausdorffness for an arbitrary bracket and Jacobi proof. The concrete abelian
example starts with no supplied representation or integrating group.

Run `python3 scripts/check_bfrf_compatibility.py` after `lake build`.
-/

noncomputable section
open BFRF.Homogeneous
open scoped Manifold ContDiff

attribute [local instance] LieRing.ofAssociativeRing

universe uE uV
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {μ : BFRF.Bracket E} {hμ : μ.Jacobi}
  {V : Type uV} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

local instance : ENat.LEInfty (minSmoothness ℝ 3) := ⟨by simp⟩

example : Nonempty (IntegratedLieGroup.{0} μ hμ) := nonempty_integratedLieGroup

example : Group (integratedLieGroup (μ := μ) (hμ := hμ)).G := inferInstance
example : LieGroup 𝓘(ℝ, E) ∞ (integratedLieGroup (μ := μ) (hμ := hμ)).G := inferInstance
example : SimplyConnectedSpace (integratedLieGroup (μ := μ) (hμ := hμ)).G := inferInstance
example : T2Space (integratedLieGroup (μ := μ) (hμ := hμ)).G := inferInstance

example : Nonempty (GroupLieAlgebra 𝓘(ℝ, E)
    (integratedLieGroup (μ := μ) (hμ := hμ)).G ≃ₗ⁅ℝ⁆ BracketLie μ hμ) :=
  ⟨(integratedLieGroup (μ := μ) (hμ := hμ)).lieEquiv⟩

example (ρ : BracketLie μ hμ →ₗ⁅ℝ⁆ Module.End ℝ V) (hρ : Function.Injective ρ) :
    Nonempty (IntegratedLieGroup.{uV} μ hμ) :=
  nonempty_integratedLieGroup_of_faithful_representation ρ hρ

example (ρ : BracketLie μ hμ →ₗ⁅ℝ⁆ Module.End ℝ V) (hρ : Function.Injective ρ) :
    T2Space (integratedLieGroupOfFaithfulRepresentation ρ hρ).G := inferInstance

example (h : LieAlgebra.center ℝ (BracketLie μ hμ) = ⊥) :
    Nonempty (IntegratedLieGroup.{uE} μ hμ) := nonempty_integratedLieGroup_of_center_eq_bot h

example (h₂ : ∀ x y z : E, μ.eval x (μ.eval y z) = 0) :
    T2Space (integratedLieGroupOfTripleLieEqZero (hμ := hμ) h₂).G := inferInstance

example (h₂ : LieModule.lowerCentralSeries ℝ (BracketLie μ hμ) (BracketLie μ hμ) 2 = ⊥) :
    Nonempty (IntegratedLieGroup.{uE} μ hμ) :=
  nonempty_integratedLieGroup_of_lowerCentralSeries_two_eq_bot h₂

example (h : Disjoint (LieAlgebra.center ℝ (BracketLie μ hμ))
    (LieAlgebra.derivedSeries ℝ (BracketLie μ hμ) 1)) :
    Nonempty (IntegratedLieGroup.{uE} μ hμ) := nonempty_integratedLieGroup_of_disjoint_center_derived h

example (h : Disjoint (LieAlgebra.center ℝ (BracketLie μ hμ))
    (LieAlgebra.derivedSeries ℝ (BracketLie μ hμ) 1)) :
    T2Space (integratedLieGroupOfDisjointCenterDerived h).G := inferInstance

example (D : LieDerivation ℝ (BracketLie μ hμ) (BracketLie μ hμ))
    (hD : ∀ x ∈ LieAlgebra.center ℝ (BracketLie μ hμ), D x = 0 → x = 0) :
    Nonempty (IntegratedLieGroup.{uE} μ hμ) :=
  nonempty_integratedLieGroup_of_derivation_injective_on_center D hD

example (D : LieDerivation ℝ (BracketLie μ hμ) (BracketLie μ hμ))
    (hD : Function.Injective D) :
    Nonempty (IntegratedLieGroup.{uE} μ hμ) := nonempty_integratedLieGroup_of_injective_derivation D hD

example (D : LieDerivation ℝ (BracketLie μ hμ) (BracketLie μ hμ))
    (hD : Function.Injective D) :
    T2Space (integratedLieGroupOfInjectiveDerivation D hD).G := inferInstance

namespace BFRFLieIIICheck

theorem zeroJacobi : (0 : BFRF.Bracket ℝ).Jacobi := by
  intro x y z
  simp [BFRF.Bracket.eval]

def abelianIntegration : IntegratedLieGroup (0 : BFRF.Bracket ℝ) zeroJacobi :=
  integratedLieGroup

example : Group abelianIntegration.G := inferInstance
example : LieGroup 𝓘(ℝ, ℝ) ∞ abelianIntegration.G := inferInstance
example : SimplyConnectedSpace abelianIntegration.G := inferInstance
example : T2Space abelianIntegration.G := by
  exact integratedLieGroupT2Space (μ := 0) (hμ := zeroJacobi)

example : Nonempty (GroupLieAlgebra 𝓘(ℝ, ℝ) abelianIntegration.G ≃ₗ⁅ℝ⁆
    BracketLie (0 : BFRF.Bracket ℝ) zeroJacobi) := ⟨abelianIntegration.lieEquiv⟩

example (x y : GroupLieAlgebra 𝓘(ℝ, ℝ) abelianIntegration.G) :
    abelianIntegration.lieEquiv ⁅x, y⁆ =
      ⁅abelianIntegration.lieEquiv x, abelianIntegration.lieEquiv y⁆ :=
  LieEquiv.map_lie _ x y

#print axioms abelianIntegration

end BFRFLieIIICheck

#print axioms IntegratedLieGroup.ofLieAlgebraIntegration
#print axioms integratedLieGroup
#print axioms nonempty_integratedLieGroup
#print axioms integratedLieGroupOfFaithfulRepresentation
#print axioms nonempty_integratedLieGroup_of_faithful_representation
#print axioms integratedLieGroupOfCenterEqBot
#print axioms nonempty_integratedLieGroup_of_center_eq_bot
#print axioms integratedLieGroupOfTripleLieEqZero
#print axioms nonempty_integratedLieGroup_of_tripleLie_eq_zero
#print axioms nonempty_integratedLieGroup_of_lowerCentralSeries_two_eq_bot
#print axioms integratedLieGroupOfDisjointCenterDerived
#print axioms nonempty_integratedLieGroup_of_disjoint_center_derived
#print axioms integratedLieGroupOfDerivationInjectiveOnCenter
#print axioms nonempty_integratedLieGroup_of_derivation_injective_on_center
#print axioms integratedLieGroupOfInjectiveDerivation
#print axioms nonempty_integratedLieGroup_of_injective_derivation
