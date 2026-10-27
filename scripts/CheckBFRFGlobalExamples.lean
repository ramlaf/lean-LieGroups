import BFRF.GlobalCorrespondence
import BFRF.LieII
import Mathlib.Analysis.Convex.Contractible

/-!
# Concrete homogeneous realizations

The zero bracket on `K × P` is integrated by the additive vector group.
Its coordinate subgroup `K × {0}` is a closed connected stabilizer. Taking
`K = ℝ` and `P = ℝ` tests positive-dimensional isotropy and quotient at once;
the stabilizer is ineffective, since it acts trivially on every quotient point.

Run `python3 scripts/check_bfrf_compatibility.py` after `lake build`.
-/

noncomputable section
open scoped Manifold ContDiff
open BFRF.Homogeneous

namespace BFRFGlobalExamples

set_option backward.isDefEq.respectTransparency false

local instance : ENat.LEInfty (minSmoothness ℝ 3) := ⟨by simp⟩

variable (K P : Type) [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ K] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P]

abbrev VectorGroup := Multiplicative (K × P)

local instance : ChartedSpace (K × P) (VectorGroup K P) :=
  inferInstanceAs (ChartedSpace (K × P) (K × P))

local instance : LieGroup 𝓘(ℝ, K × P) ∞ (VectorGroup K P) where
  toIsManifold := inferInstanceAs (IsManifold 𝓘(ℝ, K × P) ∞ (K × P))
  contMDiff_mul := by
    change ContMDiff _ _ ∞ (fun p : (K × P) × (K × P) => p.1 + p.2)
    exact contMDiff_fst.add contMDiff_snd
  contMDiff_inv := contDiff_neg.contMDiff

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem zero_jacobi : (0 : BFRF.Bracket (K × P)).Jacobi := by
  intro x y z
  simp [BFRF.Bracket.eval]

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem zero_hKK (k l : K) :
    ((0 : BFRF.Bracket (K × P)).eval (k, 0) (l, 0)).2 = 0 := by
  simp [BFRF.Bracket.eval]

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem vectorGroup_invariantField
    (v : GroupLieAlgebra 𝓘(ℝ, K × P) (VectorGroup K P)) :
    mulInvariantVectorField v = fun _ => v := by
  funext g
  change (mfderiv 𝓘(ℝ, K × P) 𝓘(ℝ, K × P) (fun x : K × P => g.toAdd + x) 0) v = v
  rw [mfderiv_eq_fderiv]
  exact congrArg (fun f : (K × P) →L[ℝ] K × P => f v)
    ((hasFDerivAt_id (𝕜 := ℝ) (0 : K × P)).const_add g.toAdd).fderiv

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem vectorGroup_bracket_zero
    (v w : GroupLieAlgebra 𝓘(ℝ, K × P) (VectorGroup K P)) : ⁅v, w⁆ = 0 := by
  rw [GroupLieAlgebra.bracket_def, vectorGroup_invariantField, vectorGroup_invariantField]
  change VectorField.mlieBracketWithin 𝓘(ℝ, K × P)
    (fun _ : K × P => v) (fun _ : K × P => w) Set.univ 0 = 0
  rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
  simp [VectorField.lieBracketWithin]

/-- The additive vector group, with its actual tangent Lie algebra identification. -/
def vectorIntegration : IntegratedLieGroup
    (0 : BFRF.Bracket (K × P)) (zero_jacobi K P) where
  G := VectorGroup K P
  group := inferInstance
  topology := inferInstance
  charted := inferInstance
  manifold := inferInstance
  lieGroup := inferInstance
  simplyConnected := inferInstanceAs (SimplyConnectedSpace (K × P))
  lieEquiv := {
    (BracketLie.toLinearEquiv 0 (zero_jacobi K P)).symm with
    map_lie' := by
      intro v w
      apply BracketLie.ext
      exact (vectorGroup_bracket_zero K P v w).trans (by simp [BFRF.Bracket.eval]) }

instance : T2Space (vectorIntegration K P).G := inferInstanceAs (T2Space (K × P))

/-- The first coordinate subgroup, retained as an actual subgroup of the integration. -/
def coordinateIsotropy : Subgroup (vectorIntegration K P).G where
  carrier := {g | g.toAdd.2 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.toAdd.2 + h.toAdd.2 = 0
    rw [hg, hh, zero_add]
  inv_mem' := by
    intro g hg
    change -g.toAdd.2 = 0
    rw [hg, neg_zero]

theorem coordinateIsotropy_connected :
    IsConnected (coordinateIsotropy K P : Set (vectorIntegration K P).G) := by
  have he : (coordinateIsotropy K P : Set (vectorIntegration K P).G) =
      Set.range (fun k : K => Multiplicative.ofAdd (k, (0 : P))) := by
    ext g
    change g.toAdd.2 = 0 ↔ ∃ k : K, (k, (0 : P)) = g.toAdd
    constructor
    · intro hg
      exact ⟨g.toAdd.1, Prod.ext rfl hg.symm⟩
    · rintro ⟨k, hk⟩
      exact (congrArg Prod.snd hk).symm
  rw [he]
  exact isConnected_range (continuous_id.prodMk continuous_const)

theorem coordinateIsotropy_closed :
    IsClosed (coordinateIsotropy K P : Set (vectorIntegration K P).G) :=
  isClosed_eq continuous_snd continuous_const

theorem coordinateIsotropy_tangent :
    HasIsotropyTangent (vectorIntegration K P) (zero_hKK K P) (coordinateIsotropy K P) := by
  intro v
  change v ∈ subgroupTangentSet (vectorIntegration K P) (coordinateIsotropy K P) ↔ v.2 = 0
  rw [subgroupTangentSet_eq_generic]
  constructor
  · rintro ⟨γ, hγ, hmem, hdiff, hderiv⟩
    let δ : ℝ → K × P := fun t => (γ t).toAdd
    have he : (fun t : ℝ => (δ t).2) = fun _ => (0 : P) := funext hmem
    have hd : DifferentiableAt ℝ δ 0 := by
      exact (mdifferentiableAt_iff_differentiableAt).mp hdiff
    have hs := hd.hasFDerivAt.snd
    have hz : (fderiv ℝ δ 0 1).2 = 0 := by
      have hh := congrArg (fun f : ℝ →L[ℝ] P => f 1) hs.fderiv
      rw [he] at hh
      simpa using hh.symm
    have hcast : (fderiv ℝ δ 0) 1 = v := by
      change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, K × P) δ 0)
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) = v at hderiv
      rw [mfderiv_eq_fderiv] at hderiv
      exact hderiv
    rw [← hcast]
    exact hz
  · intro hv
    let w : K × P := v
    let γ : ℝ → (vectorIntegration K P).G := fun t => Multiplicative.ofAdd (t • w)
    have hγ : γ 0 = 1 := by change (0 : ℝ) • w = 0; exact zero_smul ℝ w
    refine ⟨γ, hγ, ?_, ?_, ?_⟩
    · intro t
      change t • v.2 = 0
      rw [hv, smul_zero]
    · exact ((differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ))).smul_const w).mdifferentiableAt
    · change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, K × P) (fun t : ℝ => t • w) 0)
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) = w
      rw [mfderiv_eq_fderiv]
      change (fderiv ℝ (fun t : ℝ => t • w) 0) (1 : ℝ) = w
      have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const w).fderiv
      simpa using
        congrArg (fun f : ℝ →L[ℝ] K × P => f 1) hd

/-- Closed connected isotropy with the exact tangent required by BFRF. -/
def coordinateIntegratedIsotropy : IntegratedIsotropySubgroup
    (vectorIntegration K P) (zero_hKK K P) where
  Kμ := coordinateIsotropy K P
  connected := coordinateIsotropy_connected K P
  closed := coordinateIsotropy_closed K P
  tangent_isotropy := coordinateIsotropy_tangent K P

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem zero_metricIsotropy : IsMetricIsotropy (0 : BFRF.Bracket (K × P)) := by
  intro k X Y
  simp [isotropyAction_apply, BFRF.Bracket.eval]

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem zero_reductive : PreservesTangent (0 : BFRF.Bracket (K × P)) := by
  intro k X
  simp [BFRF.Bracket.eval]

/-- The initial quotient and normalized metric are constructed, rather than supplied. -/
theorem exists_initial_metric :
    ∃ R : RegularHomogeneousQuotientRealization
        (vectorIntegration K P) (coordinateIntegratedIsotropy K P),
      let Q := R.toHomogeneousQuotientRealization
      ∃ g : DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, P) Q.M,
        Q.IsInvariantMetric g ∧
        ∀ X Y : P, g.inner Q.o (Q.tangentEquiv X) (Q.tangentEquiv Y) = inner ℝ X Y := by
  obtain ⟨R, g, F, hInv, hvalue, horigin, hKilling, hanti⟩ :=
    HomogeneousQuotientRealization.exists_metric_fundamentalFields
      (KA := coordinateIntegratedIsotropy K P) (zero_metricIsotropy K P)
  exact ⟨R, g, hInv, horigin⟩

/-- The standard closed-isotropy admissibility condition holds in the explicit integration. -/
theorem vectorIntegration_admissible :
    IsAdmissible (vectorIntegration K P) (zero_hKK K P) :=
  (isAdmissible_iff_nonempty_integratedIsotropySubgroup
    (vectorIntegration K P) (zero_hKK K P)).mpr ⟨coordinateIntegratedIsotropy K P⟩

/-- Admissibility also holds for the unrestricted Lie III constructor, not only
for the explicit coordinate integration. Lie II transports the actual isotropy. -/
theorem canonicalIntegration_admissible :
    IsAdmissible (integratedLieGroup (μ := (0 : BFRF.Bracket (K × P)))
      (hμ := zero_jacobi K P)) (zero_hKK K P) := by
  let A := integratedLieGroup (μ := (0 : BFRF.Bracket (K × P))) (hμ := zero_jacobi K P)
  let Φ : IntegratedLieEquiv (vectorIntegration K P) A (LieEquiv.refl) :=
    integrateLieEquiv (LieEquiv.refl)
  have he : (BracketLie.isotropy (0 : BFRF.Bracket (K × P))
      (zero_jacobi K P) (zero_hKK K P)).map (LieEquiv.refl).toLieHom =
      BracketLie.isotropy (0 : BFRF.Bracket (K × P))
        (zero_jacobi K P) (zero_hKK K P) := by
    ext x
    simp [LieSubalgebra.mem_map]
  exact (isAdmissible_iff_nonempty_integratedIsotropySubgroup A (zero_hKK K P)).mpr
    ⟨(coordinateIntegratedIsotropy K P).map Φ he⟩

/-- The final constructor starts from the bracket and its reviewed closedness
condition, without taking an integration or a geometric realization as input. -/
theorem canonical_initial_realization :
    Nonempty (InitialHomogeneousRealization (0 : BFRF.Bracket (K × P))
      (zero_jacobi K P) (zero_hKK K P)) :=
  nonempty_initialHomogeneousRealization 0 (zero_jacobi K P) (zero_hKK K P)
    (zero_metricIsotropy K P) (canonicalIntegration_admissible K P)

/-- Initial quotient charts and local sections are outputs of the constructor. -/
def initialRegular : RegularHomogeneousQuotientRealization
    (vectorIntegration K P) (coordinateIntegratedIsotropy K P) :=
  Classical.choice (nonempty_regularHomogeneousQuotientRealization _)

omit [FiniteDimensional ℝ K] [FiniteDimensional ℝ P] in
theorem zero_transport_metricIsotropy (hp : P ≃L[ℝ] P) :
    IsMetricIsotropy
      (BFRF.Bracket.transport (blockChange hp).toLinearEquiv (0 : BFRF.Bracket (K × P))) := by
  intro k X Y
  simp only [isotropyAction_apply, BFRF.Bracket.transport_eval]
  simp [BFRF.Bracket.eval]

/-- Every change-of-frame family admits actual global targets in this example. -/
def globalExample (hp : ℝ → P ≃L[ℝ] P) (a b : ℝ) :
    ConstructedGlobalBFRealization (0 : BFRF.Bracket (K × P))
      (zero_jacobi K P) (zero_hKK K P) hp
      (initialRegular K P).toHomogeneousQuotientRealization a b :=
  coherentGlobalBFRealization (initialRegular K P) hp
    (fun t _ => zero_transport_metricIsotropy K P (hp t))

/-- The chosen quotient maps form an actual jointly smooth map on a common manifold. -/
theorem global_comparison_jointly_smooth (hp : ℝ → P ≃L[ℝ] P) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun tx : ℝ × (initialRegular K P).M =>
        (initialRegular K P).blockTransportDiffeomorph (hp tx.1) tx.2) :=
  (initialRegular K P).contMDiff_blockTransportDiffeomorph hp

/-- Both the isotropy and quotient directions are nonzero in this example. -/
theorem coordinate_isotropy_proper_nontrivial :
    coordinateIsotropy ℝ ℝ ≠ ⊥ ∧ coordinateIsotropy ℝ ℝ ≠ ⊤ := by
  constructor
  · intro h
    have hm : Multiplicative.ofAdd ((1 : ℝ), (0 : ℝ)) ∈ coordinateIsotropy ℝ ℝ := rfl
    have he := Subgroup.mem_bot.mp (h ▸ hm)
    have hh := congrArg (fun g : (vectorIntegration ℝ ℝ).G => g.toAdd.1) he
    exact one_ne_zero hh
  · intro h
    have hm : Multiplicative.ofAdd ((0 : ℝ), (1 : ℝ)) ∈ coordinateIsotropy ℝ ℝ :=
      h.symm ▸ Subgroup.mem_top _
    exact one_ne_zero hm

/-- The nontrivial-isotropy example has a nontrivial quotient carrier. -/
theorem quotient_nontrivial
    (Q : HomogeneousQuotientRealization
      (vectorIntegration ℝ ℝ) (coordinateIntegratedIsotropy ℝ ℝ)) :
    Q.π (Multiplicative.ofAdd (0, 1)) ≠ Q.o := by
  intro he
  have hm := (Q.fibre_iff (Multiplicative.ofAdd (0, 1)) 1).mp he
  change (-(0 : ℝ) + 1) = 0 at hm
  norm_num at hm

/-- The positive-dimensional stabilizer in the coordinate example is ineffective. -/
theorem coordinate_isotropy_fixes_all
    (Q : HomogeneousQuotientRealization
      (vectorIntegration K P) (coordinateIntegratedIsotropy K P))
    (k : K) (x : Q.M) : Q.act (Multiplicative.ofAdd (k, 0)) x = x := by
  obtain ⟨g, rfl⟩ := Q.π_surjective x
  rw [← Q.π_equivariant]
  apply (Q.fibre_iff _ g).mpr
  change -g.toAdd.2 + ((0 : P) + g.toAdd.2) = 0
  simp

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)

/-- The same construction includes the Lie-group case with zero isotropy. -/
example : Nonempty (RegularHomogeneousQuotientRealization
    (vectorIntegration ZeroSpace ℝ) (coordinateIntegratedIsotropy ZeroSpace ℝ)) :=
  nonempty_regularHomogeneousQuotientRealization _

example (hp : ℝ → ℝ ≃L[ℝ] ℝ) (a b : ℝ) :
    Nonempty (ConstructedGlobalBFRealization (0 : BFRF.Bracket (ZeroSpace × ℝ))
      (zero_jacobi ZeroSpace ℝ) (zero_hKK ZeroSpace ℝ) hp
      (initialRegular ZeroSpace ℝ).toHomogeneousQuotientRealization a b) :=
  ⟨globalExample ZeroSpace ℝ hp a b⟩

example (hp : ℝ → ℝ ≃L[ℝ] ℝ) (a b : ℝ) :
    Nonempty (ConstructedGlobalBFRealization (0 : BFRF.Bracket (ℝ × ℝ))
      (zero_jacobi ℝ ℝ) (zero_hKK ℝ ℝ) hp
      (initialRegular ℝ ℝ).toHomogeneousQuotientRealization a b) :=
  ⟨globalExample ℝ ℝ hp a b⟩

example : Nonempty (InitialHomogeneousRealization (0 : BFRF.Bracket (ZeroSpace × ℝ))
    (zero_jacobi ZeroSpace ℝ) (zero_hKK ZeroSpace ℝ)) :=
  canonical_initial_realization ZeroSpace ℝ

example : Nonempty (InitialHomogeneousRealization (0 : BFRF.Bracket (ℝ × ℝ))
    (zero_jacobi ℝ ℝ) (zero_hKK ℝ ℝ)) :=
  canonical_initial_realization ℝ ℝ

/-- A positive-dimensional stabilizer and quotient pass the full metric constructor. -/
example : ∃ R : RegularHomogeneousQuotientRealization
    (vectorIntegration ℝ ℝ) (coordinateIntegratedIsotropy ℝ ℝ),
    let Q := R.toHomogeneousQuotientRealization
    ∃ g : DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, ℝ) Q.M,
      Q.IsInvariantMetric g ∧
      ∀ X Y : ℝ, g.inner Q.o (Q.tangentEquiv X) (Q.tangentEquiv Y) = inner ℝ X Y :=
  exists_initial_metric ℝ ℝ

#print axioms vectorIntegration
#print axioms coordinateIsotropy_tangent
#print axioms coordinateIntegratedIsotropy
#print axioms coordinate_isotropy_proper_nontrivial
#print axioms quotient_nontrivial
#print axioms coordinate_isotropy_fixes_all
#print axioms exists_initial_metric
#print axioms vectorIntegration_admissible
#print axioms canonicalIntegration_admissible
#print axioms canonical_initial_realization
#print axioms globalExample
#print axioms global_comparison_jointly_smooth

end BFRFGlobalExamples
