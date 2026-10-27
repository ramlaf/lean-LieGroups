/-
Copyright (c) 2026 Ramiro Lafuente. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ramiro Lafuente
-/
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Torsion-free commutation along a smooth variation

These generic mixed-partial and covariant-commutation proofs are extracted and adapted
from the pinned DifferentialGeometry repository, commit
`e5037f9aab11133255430d9d7bc4137ef29df238`, files
`Geometry/Comparison/Variation/FixedChartIdentities.lean`, `FirstVariation.lean`, and
`CovariantCommutationCurvature.lean` (Apache 2.0). Only the torsion-free first-derivative
identity is needed here. The extraction avoids their unrelated curvature commutator,
Hessian, and parallel-transport-existence imports.

AI-assistance disclosure: extracted and adapted by OpenAI Codex on 2026-10-20.
-/

noncomputable section

open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace LieGroups.Analysis

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def IsSmoothVariation
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : ℝ → ℝ → M) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (fun p : ℝ × ℝ => f p.1 p.2)


section ModelCalculation

variable [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma partial_snd_apply_one (G : ℝ × ℝ → E) (u t : ℝ)
    (h : DifferentiableAt ℝ G (u, t)) :
    fderiv ℝ (fun v : ℝ => G (u, v)) t (1 : ℝ) = fderiv ℝ G (u, t) (0, 1) := by
  have hcomp : (fun v : ℝ => G (u, v)) = G ∘ (fun v : ℝ => (u, v)) := rfl
  have hincl : HasFDerivAt (fun v : ℝ => (u, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right u t
  have hG : HasFDerivAt G (fderiv ℝ G (u, t)) (u, t) := h.hasFDerivAt
  have hch := hG.comp t hincl
  rw [hcomp, hch.fderiv]
  simp [ContinuousLinearMap.inr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma partial_fst_apply_one (G : ℝ × ℝ → E) (s v : ℝ)
    (h : DifferentiableAt ℝ G (s, v)) :
    fderiv ℝ (fun u : ℝ => G (u, v)) s (1 : ℝ) = fderiv ℝ G (s, v) (1, 0) := by
  have hcomp : (fun u : ℝ => G (u, v)) = G ∘ (fun u : ℝ => (u, v)) := rfl
  have hincl : HasFDerivAt (fun u : ℝ => (u, v)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s v
  have hG : HasFDerivAt G (fderiv ℝ G (s, v)) (s, v) := h.hasFDerivAt
  have hch := hG.comp s hincl
  rw [hcomp, hch.fderiv]
  simp [ContinuousLinearMap.inl]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_jointFderiv_snd (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    deriv (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) s
      = fderiv ℝ (fderiv ℝ G) (s, t) (1, 0) (0, 1) := by
  have hg : ContDiffAt ℝ 1 (fderiv ℝ G) (s, t) := hG.fderiv_right (le_refl _)
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ G) (s, t) := hg.differentiableAt one_ne_zero
  have hincl : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s t
  have hcomp : HasFDerivAt (fun u : ℝ => fderiv ℝ G (u, t))
      ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) s :=
    hgdiff.hasFDerivAt.comp s hincl
  set L : (ℝ × ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ) with hL
  have hcomp2 : HasFDerivAt (fun u : ℝ => L (fderiv ℝ G (u, t)))
      (L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) s :=
    L.hasFDerivAt.comp s hcomp
  have hderiv : HasDerivAt (fun u : ℝ => L (fderiv ℝ G (u, t)))
      ((L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) 1) s :=
    hcomp2.hasDerivAt
  have heq : (fun u : ℝ => L (fderiv ℝ G (u, t))) =
      (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) := rfl
  rw [heq] at hderiv
  rw [hderiv.deriv]
  simp [hL, ContinuousLinearMap.inl]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_jointFderiv_fst (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    deriv (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) t
      = fderiv ℝ (fderiv ℝ G) (s, t) (0, 1) (1, 0) := by
  have hg : ContDiffAt ℝ 1 (fderiv ℝ G) (s, t) := hG.fderiv_right (le_refl _)
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ G) (s, t) := hg.differentiableAt one_ne_zero
  have hincl : HasFDerivAt (fun v : ℝ => (s, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right s t
  have hcomp : HasFDerivAt (fun v : ℝ => fderiv ℝ G (s, v))
      ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
    hgdiff.hasFDerivAt.comp t hincl
  set L : (ℝ × ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ) with hL
  have hcomp2 : HasFDerivAt (fun v : ℝ => L (fderiv ℝ G (s, v)))
      (L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ))) t :=
    L.hasFDerivAt.comp t hcomp
  have hderiv : HasDerivAt (fun v : ℝ => L (fderiv ℝ G (s, v)))
      ((L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ))) 1) t :=
    hcomp2.hasDerivAt
  have heq : (fun v : ℝ => L (fderiv ℝ G (s, v))) =
      (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) := rfl
  rw [heq] at hderiv
  rw [hderiv.deriv]
  simp [hL, ContinuousLinearMap.inr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eventually_diff_along_fst (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    ∀ᶠ u in nhds s, DifferentiableAt ℝ G (u, t) := by
  have hC1 : ContDiffAt ℝ 1 G (s, t) := hG.of_le one_le_two
  have hdiffG : ∀ᶠ p in nhds (s, t), DifferentiableAt ℝ G p :=
    (hC1.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hcont : Continuous (fun u : ℝ => (u, t)) := by continuity
  have h2 : Filter.Tendsto (fun u : ℝ => (u, t)) (nhds s) (nhds (s, t)) := by
    change ContinuousAt (fun u : ℝ => (u, t)) s
    exact hcont.continuousAt
  exact h2.eventually hdiffG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eventually_diff_along_snd (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    ∀ᶠ v in nhds t, DifferentiableAt ℝ G (s, v) := by
  have hC1 : ContDiffAt ℝ 1 G (s, t) := hG.of_le one_le_two
  have hdiffG : ∀ᶠ p in nhds (s, t), DifferentiableAt ℝ G p :=
    (hC1.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hcont : Continuous (fun v : ℝ => (s, v)) := by continuity
  have h2 : Filter.Tendsto (fun v : ℝ => (s, v)) (nhds t) (nhds (s, t)) := by
    change ContinuousAt (fun v : ℝ => (s, v)) t
    exact hcont.continuousAt
  exact h2.eventually hdiffG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_partialFderiv_snd (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    deriv (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (s, t) (1, 0) (0, 1) := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hev : (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ))
      =ᶠ[nhds s] (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) := by
    filter_upwards [eventually_diff_along_fst G s t hF] with u hu
    have hFv : (fun v : ℝ => F u v) = (fun v : ℝ => G (u, v)) := rfl
    rw [hFv]; exact partial_snd_apply_one G u t hu
  rw [hev.deriv_eq]
  exact deriv_jointFderiv_snd G s t hF

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_partialFderiv_fst (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    deriv (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (s, t) (0, 1) (1, 0) := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hev : (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ))
      =ᶠ[nhds t] (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) := by
    filter_upwards [eventually_diff_along_snd G s t hF] with v hv
    have hFu : (fun u : ℝ => F u v) = (fun u : ℝ => G (u, v)) := rfl
    rw [hFu]; exact partial_fst_apply_one G s v hv
  rw [hev.deriv_eq]
  exact deriv_jointFderiv_fst G s t hF

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma mixed_partialFderiv_comm (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    deriv (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
      = deriv (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t := by
  rw [deriv_partialFderiv_snd F s t hF, deriv_partialFderiv_fst F s t hF]
  have hsymm : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t) := by
    refine ContDiffAt.isSymmSndFDerivAt hF ?_
    rw [minSmoothness_of_isRCLikeNormedField]
  exact hsymm (1, 0) (0, 1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPulled_contDiffAt
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) := by
  have hext : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I (f s t)) (f s t) :=
    (contMDiffAt_extChartAt (I := I) (x := f s t)).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) :=
    hext.comp (s, t) hf.contMDiffAt
  have key : ContDiffAt ℝ (8 : ℕ)
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  exact key.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))

omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem commute_ds_dt_fixed_chart_C2
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (s t : ℝ)
    (hF2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t)) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t)
      (fun u : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I (f s t) (f u v)) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v)
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I (f s t) (f u v)) s (1 : ℝ)) t := by
  classical
  set α : M := f s t with hα
  set F : ℝ → ℝ → E := fun u v => extChartAt I α (f u v) with hF_def
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  have hsec :
      deriv (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
        = deriv (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t :=
    mixed_partialFderiv_comm F s t hF2
  have hcurveL : chartCurve (I := I) α (fun u : ℝ => f u t) s = F s t := rfl
  have hcurveR : chartCurve (I := I) α (fun v : ℝ => f s v) t = F s t := rfl
  have hXL : (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
      = fderiv ℝ (fun v : ℝ => F s v) t (1 : ℝ) := rfl
  have hXR : (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t
      = fderiv ℝ (fun u : ℝ => F u t) s (1 : ℝ) := rfl
  have hvelL : deriv (chartCurve (I := I) α (fun u : ℝ => f u t)) s
      = fderiv ℝ (fun u : ℝ => F u t) s (1 : ℝ) := by
    rw [← fderiv_apply_one_eq_deriv]; rfl
  have hvelR : deriv (chartCurve (I := I) α (fun v : ℝ => f s v)) t
      = fderiv ℝ (fun v : ℝ => F s v) t (1 : ℝ) := by
    rw [← fderiv_apply_one_eq_deriv]; rfl
  have hChristoffel :
      chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α (fun u : ℝ => f u t)) s)
          ((fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s)
          (chartCurve (I := I) α (fun u : ℝ => f u t) s)
        = chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α (fun v : ℝ => f s v)) t)
          ((fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t)
          (chartCurve (I := I) α (fun v : ℝ => f s v) t) := by
    rw [hvelL, hcurveL, hXL, hvelR, hcurveR, hXR]
    exact chartChristoffelContraction_symm (I := I) g α
      (fderiv ℝ (fun u : ℝ => F u t) s (1 : ℝ))
      (fderiv ℝ (fun v : ℝ => F s v) t (1 : ℝ)) (F s t)
  rw [hsec, hChristoffel]

omit [InnerProductSpace ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem commute_ds_dt_fixed_chart
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (s t : ℝ) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t)
      (fun u : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I (f s t) (f u v)) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v)
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I (f s t) (f u v)) s (1 : ℝ)) t :=
  commute_ds_dt_fixed_chart_C2 (I := I) g f s t
    (chartPulled_contDiffAt (I := I) f hf s t)


end ModelCalculation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma commute_ds_dt_intrinsic
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t := by
  classical
  set α : M := f 0 t with hα
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f s u) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f u v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun s : ℝ => f s t) := hslice_v t
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := hslice_u 0
  rw [covDerivAlong_def, covDerivAlong_def]
  have hfootL : (fun s : ℝ => f s t) 0 = α := by rw [hα]
  have hfootR : (fun v : ℝ => f 0 v) t = α := by rw [hα]
  set repL : ℝ → E := chartRepAt (I := I) (fun s : ℝ => f s t)
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 with hrepL
  set repR : ℝ → E := chartRepAt (I := I) (fun v : ℝ => f 0 v)
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t with hrepR
  set secL : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hsecL
  set secR : ℝ → E :=
    fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ) with hsecR
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H α).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H α).source} := by
    change f 0 t ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t)
  have hrepL_eq : repL =ᶠ[𝓝 (0 : ℝ)] secL := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f s u) ((hslice_u s).mdifferentiableAt (by norm_num)) α
        hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t) s) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
      = fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ)
    rw [hfootL]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  have hopenR : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t)
  have hrepR_eq : repR =ᶠ[𝓝 t] secR := by
    filter_upwards [hopenR.mem_nhds h0R] with v hv
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u v) ((hslice_v v).mdifferentiableAt (by norm_num)) α
        hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ))
      = fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    rw [hfootR]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  have hchartL : chartCovDerivAlong (I := I) g ((fun s : ℝ => f s t) 0) (fun s : ℝ => f s t) repL 0
      = chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0 := by
    rw [hfootL, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq,
      hrepL_eq.eq_of_nhds]
  have hchartR : chartCovDerivAlong (I := I) g ((fun v : ℝ => f 0 v) t) (fun v : ℝ => f 0 v) repR t
      = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t := by
    rw [hfootR, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq,
      hrepR_eq.eq_of_nhds]
  have hcommute := commute_ds_dt_fixed_chart (I := I) g f hf 0 t
  rw [show f (0 : ℝ) t = α from hα] at hcommute
  have hcommute' :
      chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0
        = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t :=
    hcommute
  rw [hchartL, hchartR]
  rw [hcommute']


open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_const_add_shift
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ s : ℝ, TangentSpace I (γ s)) (c : ℝ) :
    covDerivAlong (I := I) g (fun a : ℝ => γ (c + a))
        (fun a : ℝ => V (c + a)) 0
      = covDerivAlong (I := I) g γ V c := by
  classical
  have hfoot : γ (c + 0) = γ c := by rw [add_zero]
  have hrep : chartRepAt (I := I) (fun a : ℝ => γ (c + a)) (fun a : ℝ => V (c + a)) 0
      = (fun a : ℝ => chartRepAt (I := I) γ V c (c + a)) := by
    funext a
    rw [chartRepAt_apply, chartRepAt_apply]
    simp only [add_zero]
  have hcurve : chartCurve (I := I) (γ c) (fun a : ℝ => γ (c + a))
      = (fun a : ℝ => chartCurve (I := I) (γ c) γ (c + a)) := by
    funext a; rw [chartCurve_def, chartCurve_def]
  have hchart : chartCovDerivAlong (I := I) g (γ c) (fun a : ℝ => γ (c + a))
        (chartRepAt (I := I) (fun a : ℝ => γ (c + a)) (fun a : ℝ => V (c + a)) 0) 0
      = chartCovDerivAlong (I := I) g (γ c) γ (chartRepAt (I := I) γ V c) c := by
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrep, hcurve]
    rw [deriv_comp_const_add (chartRepAt (I := I) γ V c) c 0,
        deriv_comp_const_add (chartCurve (I := I) (γ c) γ) c 0]
    simp only [add_zero]
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [hfoot]
  rw [hchart]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma commute_ds_dt_intrinsic_shifted
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
        (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s)
      = (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t) := by
  classical
  funext s
  set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s + a) b with hfsh
  have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (s + q.1, q.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hshift
  have hcomm := commute_ds_dt_intrinsic (I := I) g fsh hfsh_smooth t
  have hLHS : covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
        (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
        (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s := by
    have hshift := covDerivAlong_const_add_shift (I := I) g (fun s' : ℝ => f s' t)
      (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s
    exact hshift
  have hbaseR : (fun v : ℝ => fsh 0 v) = (fun v : ℝ => f s v) := by funext v; rw [hfsh]; simp
  have hsecR : ∀ v : ℝ, mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh u v) 0 (1 : ℝ)
      = mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ) := by
    intro v
    have hslice_v : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
      have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
        contMDiff_id.prodMk contMDiff_const
      exact (hf : ContMDiff _ _ _ _).comp hincl
    have hcomp_eq : (fun u : ℝ => fsh u v)
        = (fun w : ℝ => f w v) ∘ (fun u : ℝ => s + u) := by funext u; simp only
                                                              [hfsh, Function.comp]
    have hψ_mdiff : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0 := by
      have hcd : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => s + u) 0 := by
        rw [contMDiffAt_iff_contDiffAt]
        exact (contDiffAt_const.add contDiffAt_id)
      exact hcd.mdifferentiableAt (by simp)
    have hφ_mdiff : MDifferentiableAt (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v)
      ((fun u : ℝ => s + u) 0) := by
      have hpt : ((fun u : ℝ => s + u) 0) = s := by simp
      rw [hpt]; exact (hslice_v.contMDiffAt).mdifferentiableAt (by simp)
    rw [hcomp_eq, mfderiv_comp 0 hφ_mdiff hψ_mdiff]
    have hderiv : HasDerivAt (fun u : ℝ => s + u) (1 : ℝ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add s
    have hψfd : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0 (1 : ℝ) = (1 : ℝ) := by
      have heq : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0
          = fderiv ℝ (fun u : ℝ => s + u) 0 :=
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := fun u : ℝ => s + u) (x := 0)
      rw [heq]
      change deriv (fun u : ℝ => s + u) 0 = (1 : ℝ)
      exact hderiv.deriv
    change mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) (s + 0)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0 (1 : ℝ)) = _
    rw [hψfd]
    rw [add_zero]
  have hRHS : covDerivAlong (I := I) g (fun v : ℝ => fsh 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh u v) 0 (1 : ℝ)) t
      = covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t := by
    rw [hbaseR]
    congr 1
    funext v; exact hsecR v
  rw [← hLHS, ← hRHS]
  exact hcomm


end LieGroups.Analysis
