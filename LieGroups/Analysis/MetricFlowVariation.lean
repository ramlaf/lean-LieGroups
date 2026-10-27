/-
Copyright (c) 2026 Ramiro Lafuente. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ramiro Lafuente
-/
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import LieGroups.Analysis.TorsionFreeVariation
import LieGroups.Analysis.MetricCompatibilityAlongCurve
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan
import DifferentialGeometry.Bundle.PartialMfderiv

/-!
# The metric variation formula for a smooth diffeomorphism flow

The derivative of the metric evaluated on two pushed-forward tangent vectors is the
metric Lie derivative evaluated on those vectors. These generic geometric results are
extracted and adapted from the pinned DifferentialGeometry repository, commit
`e5037f9aab11133255430d9d7bc4137ef29df238`, files
`Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/Variation.lean` and
`Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/Properties.lean`, and the elementary
chart-curve reparametrization from
`Geometry/Comparison/Variation/SecondVariationMinimiser.lean` (Apache 2.0).
The extraction avoids importing their Ricci-flow and parabolic-analysis application layer.
The proof uses covariant commutation of the two parameters of a smooth variation,
metric compatibility, and the Cartan formula for the metric Lie derivative.

AI-assistance disclosure: extracted and adapted by OpenAI Codex on 2026-10-20.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace LieGroups.Analysis

open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

private def reparam (r : ℝ) (s : ℝ) : ℝ :=
  (2 * r / Real.pi) * Real.arctan ((Real.pi / (2 * r)) * s)

private theorem contDiff_reparam (r : ℝ) : ContDiff ℝ ∞ (reparam r) := by
  unfold reparam
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_const.mul contDiff_id))

@[simp] private theorem reparam_zero (r : ℝ) : reparam r 0 = 0 := by
  simp [reparam, Real.arctan_zero]

private theorem abs_reparam_lt (r : ℝ) (hr : 0 < r) (s : ℝ) : |reparam r s| < r := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : (0 : ℝ) < 2 * r / Real.pi := by positivity
  rw [reparam, abs_mul, abs_of_pos hcoef]
  have harctan : |Real.arctan ((Real.pi / (2 * r)) * s)| < Real.pi / 2 :=
    abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  calc (2 * r / Real.pi) * |Real.arctan ((Real.pi / (2 * r)) * s)|
      < (2 * r / Real.pi) * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left harctan hcoef
    _ = r := by field_simp

private theorem hasDerivAt_reparam_zero (r : ℝ) (hr : 0 < r) :
    HasDerivAt (reparam r) 1 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hinner : HasDerivAt (fun s : ℝ => (Real.pi / (2 * r)) * s)
      (Real.pi / (2 * r)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (Real.pi / (2 * r))
  have harctan : HasDerivAt Real.arctan (1 / (1 + ((Real.pi / (2 * r)) * (0 : ℝ)) ^ 2))
      ((Real.pi / (2 * r)) * (0 : ℝ)) :=
    Real.hasDerivAt_arctan _
  have hcomp := harctan.comp 0 hinner
  have hscaled := hcomp.const_mul (2 * r / Real.pi)
  have hval : (2 * r / Real.pi) *
      ((1 / (1 + ((Real.pi / (2 * r)) * (0 : ℝ)) ^ 2)) * (Real.pi / (2 * r))) = 1 := by
    have hr' : (2 * r) ≠ 0 := by positivity
    have hpi' : Real.pi ≠ 0 := ne_of_gt hpi
    rw [mul_zero]
    field_simp
    ring
  have : HasDerivAt (reparam r) ((2 * r / Real.pi) *
      ((1 / (1 + ((Real.pi / (2 * r)) * (0 : ℝ)) ^ 2)) * (Real.pi / (2 * r)))) 0 := by
    rw [show reparam r = fun y =>
      (2 * r / Real.pi) * (Real.arctan ((Real.pi / (2 * r)) * y)) by rfl]
    exact hscaled
  rw [hval] at this
  exact this


variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivAlong_locality
    (g : SmoothRiemannianMetric I M) (γ₁ γ₂ : ℝ → M)
    (V₁ : ∀ s, TangentSpace I (γ₁ s)) (V₂ : ∀ s, TangentSpace I (γ₂ s)) (t : ℝ)
    (hfoot : γ₁ t = γ₂ t)
    (hγ₁ : ContinuousAt γ₁ t)
    (htot : (fun s => (TotalSpace.mk' E (γ₁ s) (V₁ s) : TangentBundle I M)) =ᶠ[𝓝 t]
      (fun s => (TotalSpace.mk' E (γ₂ s) (V₂ s) : TangentBundle I M))) :
    covDerivAlong (I := I) g γ₁ V₁ t = covDerivAlong (I := I) g γ₂ V₂ t := by
  set α : M := γ₁ t with hα
  have hbase₀ : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hpre : γ₁ ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 t :=
    hγ₁.preimage_mem_nhds (hopen.mem_nhds hbase₀)
  have hcurve_eq : γ₁ =ᶠ[𝓝 t] γ₂ := by
    filter_upwards [htot] with s hs
    exact congrArg (fun p : TangentBundle I M => p.proj) hs
  have hcurve : chartCurve (I := I) α γ₁ =ᶠ[𝓝 t] chartCurve (I := I) α γ₂ := by
    filter_upwards [hcurve_eq] with s hs
    rw [chartCurve_def, chartCurve_def, hs]
  have hrep : chartRepAt (I := I) γ₁ V₁ t =ᶠ[𝓝 t] chartRepAt (I := I) γ₂ V₂ t := by
    have hpre₂ : γ₂ ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 t := by
      filter_upwards [hpre, hcurve_eq] with s hs hseq
      simp only [Set.mem_preimage] at hs ⊢; rwa [← hseq]
    filter_upwards [htot, hpre, hpre₂] with s hs hsmem hsmem₂
    simp only [Set.mem_preimage] at hsmem hsmem₂
    have h1 : chartRepAt (I := I) γ₁ V₁ t s
        = ((trivializationAt E (TangentSpace I) α) (TotalSpace.mk' E (γ₁ s) (V₁ s))).2 := by
      rw [chartRepAt_apply, ← hα,
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_apply (R := ℝ),
        (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hsmem]
    have h2 : chartRepAt (I := I) γ₂ V₂ t s
        = ((trivializationAt E (TangentSpace I) α) (TotalSpace.mk' E (γ₂ s) (V₂ s))).2 := by
      rw [chartRepAt_apply, ← hfoot,
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_apply (R := ℝ),
        (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hsmem₂]
    rw [h1, h2, hs]
  rw [covDerivAlong_def, covDerivAlong_def, chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [← hfoot, ← hα]
  congr 1
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hcurve.deriv_eq, hcurve.eq_of_nhds]

private noncomputable def flowTimeRetract (t δ w : ℝ) (s : ℝ) : ℝ :=
  t + (s - t) * (1 - Real.smoothTransition ((s - t - δ) / w))
    * (1 - Real.smoothTransition ((t - δ - s) / w))

private lemma flowTimeRetract_contDiff (t δ w : ℝ) :
    ContDiff ℝ ∞ (flowTimeRetract t δ w) := by
  unfold flowTimeRetract
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => (1 : ℝ) - Real.smoothTransition ((s - t - δ) / w)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  have h2 : ContDiff ℝ ∞ (fun s : ℝ => (1 : ℝ) - Real.smoothTransition ((t - δ - s) / w)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  exact contDiff_const.add (((contDiff_id.sub contDiff_const).mul h1).mul h2)

private lemma flowTimeRetract_eq_self (t δ w : ℝ) (hw : 0 < w) {s : ℝ}
    (hs : s ∈ Set.Icc (t - δ) (t + δ)) :
    flowTimeRetract t δ w s = s := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold flowTimeRetract
  have hL : Real.smoothTransition ((s - t - δ) / w) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)
  have hR : Real.smoothTransition ((t - δ - s) / w) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)
  rw [hL, hR]; ring

private lemma flowTimeRetract_abs_le (t δ w : ℝ) (hδ : 0 ≤ δ) (hw : 0 < w) (s : ℝ) :
    |flowTimeRetract t δ w s - t| ≤ δ + w := by
  unfold flowTimeRetract
  rw [add_sub_cancel_left]
  by_cases hin : s ∈ Set.Icc (t - δ - w) (t + δ + w)
  · obtain ⟨hin1, hin2⟩ := hin
    have hf1 : (1 : ℝ) - Real.smoothTransition ((s - t - δ) / w) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [Real.smoothTransition.le_one ((s - t - δ) / w)],
        by linarith [Real.smoothTransition.nonneg ((s - t - δ) / w)]⟩
    have hf2 : (1 : ℝ) - Real.smoothTransition ((t - δ - s) / w) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [Real.smoothTransition.le_one ((t - δ - s) / w)],
        by linarith [Real.smoothTransition.nonneg ((t - δ - s) / w)]⟩
    rw [abs_mul, abs_mul]
    have hb1 : |(1 : ℝ) - Real.smoothTransition ((s - t - δ) / w)| ≤ 1 := by
      rw [abs_of_nonneg hf1.1]; exact hf1.2
    have hb2 : |(1 : ℝ) - Real.smoothTransition ((t - δ - s) / w)| ≤ 1 := by
      rw [abs_of_nonneg hf2.1]; exact hf2.2
    have hsdt : |s - t| ≤ δ + w := by rw [abs_le]; constructor <;> linarith
    calc |s - t| * |(1 : ℝ) - Real.smoothTransition ((s - t - δ) / w)|
            * |(1 : ℝ) - Real.smoothTransition ((t - δ - s) / w)|
        ≤ (δ + w) * 1 * 1 := by
          apply mul_le_mul (mul_le_mul hsdt hb1 (abs_nonneg _) (by linarith)) hb2 (abs_nonneg _)
          positivity
      _ = δ + w := by ring
  · rw [Set.mem_Icc, not_and_or] at hin
    have hzero : (s - t) * (1 - Real.smoothTransition ((s - t - δ) / w))
        * (1 - Real.smoothTransition ((t - δ - s) / w)) = 0 := by
      rcases hin with h | h
      · have hlt : s < t - δ - w := lt_of_not_ge h
        have : Real.smoothTransition ((t - δ - s) / w) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [le_div_iff₀ hw]; linarith
        rw [this]; ring
      · have hlt : t + δ + w < s := lt_of_not_ge h
        have : Real.smoothTransition ((s - t - δ) / w) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [le_div_iff₀ hw]; linarith
        rw [this]; ring
    rw [hzero, abs_zero]; linarith

private lemma flowTimeRetract_mem_Ioo (t T δ w : ℝ) (hδ : 0 ≤ δ) (hw : 0 < w)
    (hlo : 0 < t - (δ + w)) (hhi : t + (δ + w) < T) (s : ℝ) :
    flowTimeRetract t δ w s ∈ Set.Ioo (0 : ℝ) T := by
  have h := flowTimeRetract_abs_le t δ w hδ hw s
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private noncomputable def chartLineCurve (x : M) (v : TangentSpace I x) (δ : ℝ) : ℝ → M :=
  fun r => (extChartAt I x).symm
    (extChartAt I x x + (reparam δ r) • tangentSpaceModelContinuousLinearEquiv (I := I) x v)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma exists_chartLineCurve_global
    (x : M) (v : TangentSpace I x) :
    ∃ δ : ℝ, 0 < δ ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ (chartLineCurve (I := I) x v δ) ∧
      chartLineCurve (I := I) x v δ 0 = x ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) I (chartLineCurve (I := I) x v δ) 0
        (tangentLinearMapOfModel (I := 𝓘(ℝ, ℝ)) (I' := I)
          (x := 0) (y := chartLineCurve (I := I) x v δ 0)
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (tangentSpaceModelContinuousLinearEquiv (I := I) x v))) := by
  classical
  set φ : E := extChartAt I x x with hφ
  set vE : E := tangentSpaceModelContinuousLinearEquiv (I := I) x v with hvE
  set L : ℝ → E := fun t : ℝ => φ + t • vE with hL
  have hLcont : Continuous L := by fun_prop
  have hL0 : L 0 = φ := by simp [hL]
  have htgt : (extChartAt I x).target ∈ 𝓝 φ := by
    rw [hφ]; exact extChartAt_target_mem_nhds x
  have hpre : L ⁻¹' (extChartAt I x).target ∈ 𝓝 (0 : ℝ) := by
    have := hLcont.continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, hL0] at this
    exact this htgt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hcurve : chartLineCurve (I := I) x v ε =
      fun r : ℝ => (extChartAt I x).symm (φ + (reparam ε r) • vE) := by
    funext r
    simp only [chartLineCurve, hφ, hvE]
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · have hreparam : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r : ℝ => φ + (reparam ε r) • vE) := by
      rw [contMDiff_iff_contDiff]
      have : ContDiff ℝ ∞ (fun r : ℝ => φ + (reparam ε r) • vE) :=
        contDiff_const.add ((contDiff_reparam ε).smul contDiff_const)
      simpa using this
    have hmaps : ∀ r : ℝ, (fun r : ℝ => φ + (reparam ε r) • vE) r ∈ (extChartAt I x).target := by
      intro r
      have hin : (reparam ε r) ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact abs_reparam_lt ε hε r
      have := hball hin
      simpa [hL] using this
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (extChartAt I x).target :=
      contMDiffOn_extChartAt_symm (n := (∞ : WithTop ℕ∞)) x
    have hcomp := hsymm.comp_contMDiff hreparam hmaps
    rw [hcurve]
    exact hcomp
  · simp [chartLineCurve, reparam_zero]
  · have hLine : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => φ + (reparam ε r) • vE) 0
        (modelLinearMapToTangent
          (A := (1 : ℝ →L[ℝ] ℝ).smulRight vE)) := by
      have hrd : HasDerivAt (reparam ε) 1 0 := hasDerivAt_reparam_zero ε hε
      have hsmul : HasDerivAt (fun r : ℝ => (reparam ε r) • vE) ((1 : ℝ) • vE) 0 := by
        have := hrd.smul_const vE
        simpa using this
      have hadd0 : HasDerivAt (fun r : ℝ => φ + (reparam ε r) • vE) (0 + (1 : ℝ) • vE) 0 :=
        (hasDerivAt_const (0 : ℝ) φ).add hsmul
      rw [zero_add, one_smul] at hadd0
      exact HasFDerivAt.hasMFDerivAt_model hadd0.hasFDerivAt
    have hsymmD : HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I x).symm φ
        (tangentLinearMapOfModel (I := 𝓘(ℝ, E)) (I' := I)
          (x := φ) (y := (extChartAt I x).symm φ) (ContinuousLinearMap.id ℝ E)) := by
      have hmem : φ ∈ (extChartAt I x).target := by rw [hφ]; exact mem_extChartAt_target x
      have hdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ := by
        have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x) hmem
        rwa [I.range_eq_univ] at this
      have heq : tangentLinearMapToModel
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm univ φ) =
          ContinuousLinearMap.id ℝ E := by
        rw [hφ, ← I.range_eq_univ]
        have hraw := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
        exact congrArg tangentLinearMapToModel hraw
      have heqNative : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm univ φ =
          tangentLinearMapOfModel (I := 𝓘(ℝ, E)) (I' := I)
            (x := φ) (y := (extChartAt I x).symm φ) (ContinuousLinearMap.id ℝ E) := by
        apply tangentLinearMapToModel_injective
        rw [heq, tangentLinearMapToModel_ofModel]
      rw [← hasMFDerivWithinAt_univ]
      exact heqNative ▸ hdiff.hasMFDerivWithinAt
    have hLine0 : (fun r : ℝ => φ + (reparam ε r) • vE) 0 = φ := by
      simp [reparam_zero]
    have hcomp := (hLine0.symm ▸ hsymmD).comp 0 hLine
    rw [Function.comp_def] at hcomp
    have hmap :
        (tangentLinearMapOfModel (I := 𝓘(ℝ, E)) (I' := I)
          (x := (fun r : ℝ => φ + (reparam ε r) • vE) 0)
          (y := (extChartAt I x).symm ((fun r : ℝ => φ + (reparam ε r) • vE) 0))
          (ContinuousLinearMap.id ℝ E)).comp
            (modelLinearMapToTangent
              (A := (1 : ℝ →L[ℝ] ℝ).smulRight vE)) =
          tangentLinearMapOfModel (I := 𝓘(ℝ, ℝ)) (I' := I)
            (x := 0)
            (y := (extChartAt I x).symm ((fun r : ℝ => φ + (reparam ε r) • vE) 0))
            ((1 : ℝ →L[ℝ] ℝ).smulRight vE) := by
      apply tangentLinearMapToModel_injective
      rw [tangentLinearMapToModel_comp, tangentLinearMapToModel_ofModel,
        tangentLinearMapToModel_modelLinearMapToTangent, ContinuousLinearMap.id_comp,
        tangentLinearMapToModel_ofModel]
    rw [hmap] at hcomp
    rw [hcurve]
    simpa [hLine0, hvE] using hcomp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem flow_cov_variation
    (g : SmoothRiemannianMetric I M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) t).toContinuousLinearMap.smulRight
            (-(X t ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    covDerivAlong (I := I) g (fun s : ℝ => (Φ_fam s : M → M) x)
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) t =
      -((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
        ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)) := by
  classical
  obtain ⟨ht0, htT⟩ := ht
  obtain ⟨δc, hδc, hcc_smooth, hcc0, hcc_vel⟩ := exists_chartLineCurve_global (I := I) x v
  set cc : ℝ → M := chartLineCurve (I := I) x v δc with hcc_def
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  have hcc_mderiv : mfderiv 𝓘(ℝ, ℝ) I cc 0
      (constantModelVectorField (1 : ℝ) 0) = v := by
    rw [hcc_vel.mfderiv]
    rw [hcc0]
    simp [tangentLinearMapOfModel, constantModelVectorField]
  have hcc_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I cc 0 :=
    hcc_smooth.contMDiffAt.mdifferentiableAt (by simp)
  set η : ℝ := min t (T - t) / 4 with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]; have : 0 < min t (T - t) := lt_min ht0 (by linarith); positivity
  have hsum_lt : η + η < min t (T - t) := by
    rw [hη_def]; have : 0 < min t (T - t) := lt_min ht0 (by linarith); linarith
  have hlo : 0 < t - (η + η) := by
    have := lt_of_lt_of_le hsum_lt (min_le_left _ _); linarith
  have hhi : t + (η + η) < T := by
    have := lt_of_lt_of_le hsum_lt (min_le_right _ _); linarith
  set ρ : ℝ → ℝ := flowTimeRetract t η η with hρ_def
  have hρ_mem : ∀ s : ℝ, ρ s ∈ Set.Ioo (0 : ℝ) T := fun s =>
    flowTimeRetract_mem_Ioo t T η η (le_of_lt hη_pos) hη_pos hlo hhi s
  have hρ_eq : ∀ s ∈ Set.Icc (t - η) (t + η), ρ s = s := fun s hs =>
    flowTimeRetract_eq_self t η η hη_pos hs
  have hρt : ρ t = t := hρ_eq t ⟨by linarith, by linarith⟩
  have hρ_nhds : (fun s : ℝ => ρ s) =ᶠ[𝓝 t] (fun s : ℝ => s) := by
    have hmem : Set.Icc (t - η) (t + η) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with s hs using hρ_eq s hs
  have hρ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := by
    rw [contMDiff_iff_contDiff]; exact flowTimeRetract_contDiff t η η
  set Gg : ℝ → ℝ → M := fun s r => (Φ_fam (ρ s) : M → M) (cc r) with hGg_def
  have hGg_var : IsSmoothVariation (I := I) Gg := by
    have hρ8 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) ρ := hρ_smooth.of_le h8le
    have hcc8 : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) cc := hcc_smooth.of_le h8le
    have hinner : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun p : ℝ × ℝ => (ρ p.1, cc p.2)) :=
      (hρ8.comp contMDiff_fst).prodMk (hcc8.comp contMDiff_snd)
    have hmaps : ∀ p : ℝ × ℝ, (ρ p.1, cc p.2) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) :=
      fun p => ⟨hρ_mem p.1, Set.mem_univ _⟩
    have hjoint8 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
      hjoint.of_le h8le
    have hcomp := hjoint8.comp_contMDiff hinner hmaps
    exact (hcomp : ContMDiff _ _ _ _)
  have hchain : ∀ u : ℝ,
      mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam u : M → M) (cc w)) 0
        (constantModelVectorField (1 : ℝ) 0)
        = mfderiv I I (Φ_fam u : M → M) x v := by
    intro u
    have hg : MDifferentiableAt I I (Φ_fam u : M → M) (cc 0) :=
      (((Φ_fam u).contMDiff).contMDiffAt).mdifferentiableAt (by simp)
    have hcompeq : (fun w : ℝ => (Φ_fam u : M → M) (cc w)) = (Φ_fam u : M → M) ∘ cc := rfl
    rw [hcompeq, mfderiv_comp 0 hg hcc_mdiff, ContinuousLinearMap.comp_apply,
      hcc_mderiv, hcc0]
  have horbit_nhds : ∀ r : ℝ,
      (fun w : ℝ => Gg w r) =ᶠ[𝓝 t] (fun w : ℝ => (Φ_fam w : M → M) (cc r)) := by
    intro r
    filter_upwards [hρ_nhds] with w hw
    simp only [hGg_def]
    rw [hw]
  have hsec : ∀ r : ℝ,
      mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg w r) t
        (constantModelVectorField (1 : ℝ) t)
        = -(X t ((Φ_fam t : M → M) (cc r))) := by
    intro r
    have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam w : M → M) (cc r)) t
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) t).toContinuousLinearMap.smulRight
            (-(X t ((Φ_fam t : M → M) (cc r))))) :=
      (hΦode (cc r) t ⟨ht0, htT⟩).hasMFDerivAt (Ici_mem_nhds ht0)
    have hG := hmf.congr_of_eventuallyEq_abuse (horbit_nhds r)
    rw [hG.mfderiv]
    have heval :
        (((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) t).toContinuousLinearMap.smulRight
            (-(X t ((Φ_fam t : M → M) (cc r)))))
          (constantModelVectorField (1 : ℝ) t)) =
            -(X t ((Φ_fam t : M → M) (cc r))) := by
      rw [ContinuousLinearMap.smulRight_apply]
      simp [constantModelVectorField]
    exact heval
  have hGg0 : ∀ s : ℝ, Gg s 0 = (Φ_fam (ρ s) : M → M) x := by
    intro s; simp only [hGg_def]; rw [hcc0]
  have hbundle : ∀ u : ℝ,
      (TotalSpace.mk' E ((Φ_fam u : M → M) (cc 0))
          (mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam u : M → M) (cc w)) 0
            (constantModelVectorField (1 : ℝ) 0))
          : TangentBundle I M)
        = TotalSpace.mk' E ((Φ_fam u : M → M) x) (mfderiv I I (Φ_fam u : M → M) x v) := by
    intro u
    have hbase : (Φ_fam u : M → M) (cc 0) = (Φ_fam u : M → M) x := by rw [hcc0]
    rw [hchain u, hbase]
  have hcomm := commute_ds_dt_intrinsic_shifted (I := I) g Gg hGg_var 0
  have hcomm_t := congrFun hcomm t
  have hfoot_t : Gg t 0 = (Φ_fam t : M → M) x := by rw [hGg0 t, hρt]
  have hL : covDerivAlong (I := I) g (fun s' : ℝ => Gg s' 0)
        (fun s' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg s' w) 0
          (constantModelVectorField (1 : ℝ) 0)) t
      = covDerivAlong (I := I) g (fun s' : ℝ => (Φ_fam s' : M → M) x)
        (fun s' : ℝ => mfderiv I I (Φ_fam s' : M → M) x v) t := by
    refine covDerivAlong_locality (I := I) g (fun s' : ℝ => Gg s' 0)
      (fun s' : ℝ => (Φ_fam s' : M → M) x) _ _ t hfoot_t ?_ ?_
    · have hslice : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun s' : ℝ => Gg s' 0) :=
        (hGg_var : ContMDiff _ _ _ _).comp (contMDiff_id.prodMk contMDiff_const)
      exact hslice.continuous.continuousAt
    · filter_upwards [hρ_nhds] with s' hs'
      have hslice : (fun w : ℝ => Gg s' w) = (fun w : ℝ => (Φ_fam s' : M → M) (cc w)) := by
        funext w; simp only [hGg_def]; rw [hs']
      have hpt : Gg s' 0 = (Φ_fam s' : M → M) (cc 0) := by simp only [hGg_def, hs']
      calc (TotalSpace.mk' E (Gg s' 0)
              (mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg s' w) 0
                (constantModelVectorField (1 : ℝ) 0)) : TangentBundle I M)
          = TotalSpace.mk' E ((Φ_fam s' : M → M) (cc 0))
              (mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam s' : M → M) (cc w)) 0
                (constantModelVectorField (1 : ℝ) 0)) :=
            congrArg (fun g : ℝ → M =>
              (TotalSpace.mk' E (g 0) (mfderiv 𝓘(ℝ, ℝ) I g 0
                (constantModelVectorField (1 : ℝ) 0)) : TangentBundle I M)) hslice
        _ = TotalSpace.mk' E ((Φ_fam s' : M → M) x) (mfderiv I I (Φ_fam s' : M → M) x v) :=
            hbundle s'
  have hR : covDerivAlong (I := I) g (fun r : ℝ => Gg t r)
        (fun r : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg w r) t
          (constantModelVectorField (1 : ℝ) t)) 0
      = -((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
        ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)) := by
    have hRb : ∀ r : ℝ, Gg t r = (Φ_fam t : M → M) (cc r) := by
      intro r; simp only [hGg_def, hρt]
    have hstep1 : covDerivAlong (I := I) g (fun r : ℝ => Gg t r)
          (fun r : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg w r) t
            (constantModelVectorField (1 : ℝ) t)) 0
        = covDerivAlong (I := I) g (fun r : ℝ => (Φ_fam t : M → M) (cc r))
          (fun r : ℝ => -(X t ((Φ_fam t : M → M) (cc r)))) 0 := by
      refine covDerivAlong_locality (I := I) g (fun r : ℝ => Gg t r)
        (fun r : ℝ => (Φ_fam t : M → M) (cc r)) _ _ 0 (hRb 0) ?_ ?_
      · have hslice : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun r : ℝ => Gg t r) :=
          (hGg_var : ContMDiff _ _ _ _).comp (contMDiff_const.prodMk contMDiff_id)
        exact hslice.continuous.continuousAt
      · filter_upwards with r
        rw [hsec r, hRb r]
    rw [hstep1]
    have hneg : (fun r : ℝ => -(X t ((Φ_fam t : M → M) (cc r))))
        = (fun r : ℝ => (-1 : ℝ) • X t ((Φ_fam t : M → M) (cc r))) := by
      funext r; rw [neg_one_smul]
    rw [hneg, covDerivAlong_smul]
    have hleaf5 : covDerivAlong (I := I) g
          (fun r : ℝ => (Φ_fam t : M → M) (cc r))
          (fun r : ℝ => X t ((Φ_fam t : M → M) (cc r))) 0
        = (LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
          ((Φ_fam t : M → M) (cc 0))
          (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => (Φ_fam t : M → M) (cc r)) 0
            (constantModelVectorField (1 : ℝ) 0)) := by
      have hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun r : ℝ => (Φ_fam t : M → M) (cc r)) :=
        ((Φ_fam t).contMDiff).comp hcc_smooth
      exact covDerivAlong_restrict_eq_leviCivita (I := I) g
        (fun r : ℝ => (Φ_fam t : M → M) (cc r))
        (X t : ∀ y : M, TangentSpace I y) 0 hγsmooth
        (X t).mdifferentiableAt
    rw [hleaf5, hchain t, hcc0]
    rw [neg_one_smul]
  exact hL.symm.trans (hcomm_t.trans hR)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem spatial_pushforward_chartCoord_contMDiffAt
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (5 : ℕ)
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
          ((Φ_fam p.2 : M → M) x) (mfderiv I I (Φ_fam p.2 : M → M) x v)) (t, t) := by
  classical
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  set α : M := (Φ_fam t : M → M) x with hα
  have hflow_at : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I (8 : ℕ)
      (Function.uncurry (fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y)) ((t, t), x) := by
    have hcompfun : (Function.uncurry (fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y))
        = (fun r : ((ℝ × ℝ) × M) => (Φ_fam r.1.2 : M → M) r.2) := rfl
    rw [hcompfun]
    have hmaps : (fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)
        ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := ⟨ht, Set.mem_univ _⟩
    have hmem_nhds : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M)
        ∈ nhds ((fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds hmaps
    have hjoint_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
        ((fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)) :=
      ((hjoint.of_le h8le).contMDiffAt hmem_nhds)
    have hinner : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x) :=
      (contMDiffAt_fst.snd).prodMk contMDiffAt_snd
    exact hjoint_at.comp ((t, t), x) hinner
  have h_smooth_mfd := ContMDiffAt.mfderiv_apply
    (I := I) (I' := I)
    (f := fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y)
    (g := fun _ : ℝ × ℝ => x)
    (g₁ := id) (g₂ := fun _ : ℝ × ℝ => v)
    (x₀ := (t, t)) (n := (8 : ℕ)) (m := (5 : ℕ))
    (by simpa using hflow_at) contMDiffAt_const contMDiffAt_id contMDiffAt_const
    (by exact_mod_cast (by norm_num : (5 : ℕ) + 1 ≤ 8))
  refine h_smooth_mfd.congr_of_eventuallyEq ?_
  have hcontAt : ContinuousAt (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) (t, t) := by
    have hflowAt : ContinuousAt (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) := by
      have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
      exact (hjoint.continuousOn.continuousAt hmem)
    have hcomp : ContinuousAt (fun p : ℝ × ℝ => ((p.2, x) : ℝ × M)) (t, t) :=
      (continuous_snd.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (x := (t, t)) (by simpa using hflowAt) hcomp
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hpre : (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) ⁻¹' (chartAt H α).source ∈ nhds (t, t) :=
    hcontAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds (by rw [hα]; exact hαsrc))
  filter_upwards [hpre] with p hp
  have hxsrc : (id ((fun _ : ℝ × ℝ => x) p)) ∈
    (chartAt H ((fun _ : ℝ × ℝ => x) (t, t))).source := by
    simp [mem_chart_source]
  have hysrc : ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p)
      ∈ (chartAt H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) (t, t))).source := by
    simpa [hα] using hp
  symm
  simp only [id_eq]
  rw [inTangentCoordinates_eq (I := I) (I' := I)
        (f := fun _ : ℝ × ℝ => x) (g := fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x)
        (ϕ := fun q : ℝ × ℝ => mfderiv I I (fun y : M => (Φ_fam q.2 : M → M) y) x) hxsrc hysrc]
  have htarget_eq : (tangentBundleCore I M).coordChange
        (achart H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p))
        (achart H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) (t, t)))
        ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p)
      = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
        ((Φ_fam p.2 : M → M) x) := by
    change (tangentBundleCore I M).coordChange (achart H ((Φ_fam p.2 : M → M) x)) (achart H α)
        ((Φ_fam p.2 : M → M) x)
      = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
    have hsrcα : (Φ_fam p.2 : M → M) x ∈ (chartAt H α).source := hp
    exact (TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (b₀ := α) (b := (Φ_fam p.2 : M → M) x) hsrcα).symm
  rw [htarget_eq]
  change (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
      ((Φ_fam p.2 : M → M) x)
        (mfderiv I I (Φ_fam p.2 : M → M) x
          ((tangentBundleCore I M).coordChange (achart H x) (achart H x) x v)) =
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
      ((Φ_fam p.2 : M → M) x) (mfderiv I I (Φ_fam p.2 : M → M) x v)
  rw [show ((tangentBundleCore I M).coordChange (achart H x) (achart H x) x) v = v from
    (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v]


open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem flow_slot_deriv
    (g : SmoothRiemannianMetric I M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X t ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      (- lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  classical
  set γ : ℝ → M := fun s : ℝ => (Φ_fam s : M → M) x with hγ
  set V : ∀ s : ℝ, TangentSpace I (γ s) := fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v with hV
  set W : ∀ s : ℝ, TangentSpace I (γ s) := fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x w with hW
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  have hchartRepDiff : ∀ u : TangentSpace I x,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x u) t) t := by
    intro u
    have hlin := spatial_pushforward_chartCoord_contMDiffAt (I := I) T Φ_fam hjoint t ht x u
    have hrestr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (5 : ℕ)
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t := by
      have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (5 : ℕ)
          (fun s : ℝ => (t, s)) t := contMDiffAt_const.prodMk contMDiffAt_id
      exact hlin.comp t hincl
    have hcd : ContDiffAt ℝ (5 : ℕ)
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t := by
      rw [← contMDiffAt_iff_contDiffAt]; exact hrestr
    have hdiffAt : DifferentiableAt ℝ
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t :=
      hcd.differentiableAt (by norm_num)
    have hfun : chartRepAt (I := I) γ (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x u) t
        = (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) := by
      funext s; rw [chartRepAt_apply]
    rw [hfun]; exact hdiffAt
  have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) γ t := by
    have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
    have hflow_tx : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) :=
      (hjoint.of_le h8le).contMDiffAt hmem
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun s : ℝ => ((s, x) : ℝ × M)) t := contMDiffAt_id.prodMk contMDiffAt_const
    exact ContMDiffAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (x := t)
      (by simpa using hflow_tx) hincl
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t) γ) t := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (8 : ℕ) ((extChartAt I (γ t)) ∘ γ) t := by
      have hφ : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I (γ t)) (γ t) :=
        (contMDiffAt_extChartAt (I := I) (x := γ t)).of_le h8le
      exact hφ.comp t hγ_at
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hmc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I)
    g γ V W t hγ_at.continuousAt hchartDeriv (hchartRepDiff v) (hchartRepDiff w)
  have hG2v := flow_cov_variation (I := I) g X T Φ_fam hΦode hjoint t ht x v
  have hG2w := flow_cov_variation (I := I) g X T Φ_fam hΦode hjoint t ht x w
  have hAval : g.inner (γ t) (covDerivAlong (I := I) g γ V t) (W t)
      = -g.inner ((Φ_fam t : M → M) x)
          ((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
            ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x v))
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hV, hG2v, map_neg]; rfl
  have hBval : g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W t)
      = -g.inner ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          ((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
            ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x w)) := by
    rw [hW, hG2w, map_neg]
  have hsumval : g.inner (γ t) (covDerivAlong (I := I) g γ V t) (W t)
        + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W t)
      = -lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hAval, hBval]
    rw [DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
    ring
  have hmc' : HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (-lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)) t := by
    rw [← hsumval]; exact hmc
  exact hmc'.hasDerivWithinAt

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem flow_slot_pos
    (g : SmoothRiemannianMetric I M)
    (Y : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t ((Φ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (lieDerivMetric (I := I) g (Y t) ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  have hneg : ∀ z : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-((-Y s) ((Φ_fam s : M → M) z)))) := by
    intro z s hs
    simpa using hΦode z s hs
  have h := flow_slot_deriv (I := I) g (fun s => -Y s) T Φ_fam hneg hjoint
    t ht x v w
  convert h using 1
  rw [show -Y t = (-1 : ℝ) • Y t by simp,
    lieDerivMetric_smul_vectorField]
  ring


end LieGroups.Analysis
