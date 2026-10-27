/-
Copyright (c) 2026 Ramiro Lafuente. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ramiro Lafuente
-/
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong

/-!
# Metric compatibility along curves

The derivative of the metric pairing of two differentiable vector fields along a curve
is the sum of their covariant derivative pairings. This theorem is extracted without
geodesic or parallel-transport existence dependencies from the pinned
DifferentialGeometry repository, commit `e5037f9aab11133255430d9d7bc4137ef29df238`,
`Geometry/Comparison/Variation/FirstVariation.lean`, lines 49–197 (Apache 2.0).
The genuine chart computation and proof of metric compatibility are retained.

AI-assistance disclosure: extracted and adapted by OpenAI Codex on 2026-10-20.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace LieGroups.Analysis

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma metric_compat_hasDerivAt_inner_of_chartCurveDeriv
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ)
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_chartDeriv :
      DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀)
    (hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)) t₀ := by
  classical
  set α : M := γ t₀ with hα_def
  set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
  set Wrep : ℝ → E := chartRepAt (I := I) γ W t₀ with hWrep_def
  have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ t₀)
  have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
    hγ_cont (hbaseSet_open.mem_nhds hbase_t₀)
  have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
      (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
    intro s hs
    simpa [hVrep_def, chartRepAt_apply] using
      (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (V s)
  have hWround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
      (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s) = W s := by
    intro s hs
    simpa [hWrep_def, chartRepAt_apply] using
      (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (W s)
  set f : ℝ → ℝ := fun s => g.inner (γ s) (V s) (W s) with hf_def
  have hf_eq : f =ᶠ[𝓝 t₀]
      fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep Wrep s := by
    filter_upwards [hsrc_mem] with s hs
    have hVs := hVround s hs
    have hWs := hWround s hs
    have hfs : f s = g.inner (γ s)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s)) := by
      rw [hf_def]; rw [hVs, hWs]
    rw [hfs, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (Wrep s)]
    rw [AlongCurve.chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
      rw [chartCurve_def]
      refine (extChartAt I α).left_inv ?_
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      rw [TangentBundle.trivializationAt_baseSet] at hs
      exact hs
    rw [DifferentialGeometry.Geometry.Operator.chartGramOnE_def, hinv]
  have hu_hasDerivAt : HasDerivAt (chartCurve (I := I) α γ)
      (deriv (chartCurve (I := I) α γ) t₀) t₀ :=
    hγ_chartDeriv.hasDerivAt
  have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
    have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
    exact
      Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α ((extChartAt I α).map_source hxsrc)
  have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ := hVdiff.hasDerivAt
  have hWrep_hasDerivAt : HasDerivAt Wrep (deriv Wrep t₀) t₀ := hWdiff.hasDerivAt
  have hgram := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep Wrep
    (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
    (Vprime := fun _ => deriv Vrep t₀)
    (Wprime := fun _ => deriv Wrep t₀)
    hu_hasDerivAt hmem_int hVrep_hasDerivAt hWrep_hasDerivAt
  have hbase_set0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hDVchart :
      deriv Vrep t₀ +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
          (chartCurve (I := I) α γ t₀)
        = chartCovDerivAlong (I := I) g α γ Vrep t₀ := by
    rw [chartCovDerivAlong_def]
  have hDWchart :
      deriv Wrep t₀ +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t₀) (Wrep t₀)
          (chartCurve (I := I) α γ t₀)
        = chartCovDerivAlong (I := I) g α γ Wrep t₀ := by
    rw [chartCovDerivAlong_def]
  have hDV_eq : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
        (covDerivAlong (I := I) g γ V t₀)
      = chartCovDerivAlong (I := I) g α γ Vrep t₀ := by
    have := covDerivAlong_chartCoord (I := I) g γ V t₀
    rw [hα_def, hVrep_def]; exact this
  have hDW_eq : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
        (covDerivAlong (I := I) g γ W t₀)
      = chartCovDerivAlong (I := I) g α γ Wrep t₀ := by
    have := covDerivAlong_chartCoord (I := I) g γ W t₀
    rw [hα_def, hWrep_def]; exact this
  have hVt₀_coord : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (V t₀) = Vrep
    t₀ := by
    rw [hVrep_def, chartRepAt_apply, hα_def]
  have hWt₀_coord : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (W t₀) = Wrep
    t₀ := by
    rw [hWrep_def, chartRepAt_apply, hα_def]
  have hrtV : (trivializationAt E (TangentSpace I) α).symmL ℝ α (Vrep t₀) = V t₀ := by
    rw [← hVt₀_coord]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtW : (trivializationAt E (TangentSpace I) α).symmL ℝ α (Wrep t₀) = W t₀ := by
    rw [← hWt₀_coord]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtDV : (trivializationAt E (TangentSpace I) α).symmL ℝ α
        (chartCovDerivAlong (I := I) g α γ Vrep t₀)
      = covDerivAlong (I := I) g γ V t₀ := by
    rw [← hDV_eq]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtDW : (trivializationAt E (TangentSpace I) α).symmL ℝ α
        (chartCovDerivAlong (I := I) g α γ Wrep t₀)
      = covDerivAlong (I := I) g γ W t₀ := by
    rw [← hDW_eq]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  set u0 : E := chartCurve (I := I) α γ t₀ with hu0_def
  have hu0_eq : u0 = extChartAt I α α := by
    rw [hu0_def, chartCurve_def, hα_def]
  have hGram_eq : ∀ l j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α l j u0
        = chartGramMatrix (I := I) g α α l j := by
    intro l j
    rw [DifferentialGeometry.Geometry.Operator.chartGramOnE_def, hu0_eq,
      (extChartAt I α).left_inv (mem_extChartAt_source α)]
  have hinnerDV :
      g.inner α (covDerivAlong (I := I) g γ V t₀) (W t₀)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α l j u0
              * chartCoord (E := E) l (chartCovDerivAlong (I := I) g α γ Vrep t₀)
              * chartCoord (E := E) j (Wrep t₀) := by
    rw [← hrtDV, ← hrtW, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α _ _]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hGram_eq l j]
  have hinnerDW :
      g.inner α (V t₀) (covDerivAlong (I := I) g γ W t₀)
        = ∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α i l u0
              * chartCoord (E := E) i (Vrep t₀)
              * chartCoord (E := E) l (chartCovDerivAlong (I := I) g α γ Wrep t₀) := by
    rw [← hrtV, ← hrtDW, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α _ _]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hGram_eq i l]
  refine (hgram.congr_of_eventuallyEq hf_eq).congr_deriv ?_
  rw [hinnerDV, hinnerDW]
  simp only [← hDVchart, ← hDWchart]

end LieGroups.Analysis
