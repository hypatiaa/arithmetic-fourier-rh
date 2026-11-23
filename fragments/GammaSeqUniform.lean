import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Tactic

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RHConnections.GammaSeqUniform

private def approximand (n : ℕ) (s : ℂ) : ℝ → ℂ :=
  (Ioc 0 (n : ℝ)).indicator fun x : ℝ =>
    (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)

private theorem approximand_integrable (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (approximand n s) (volume.restrict (Ioi 0)) := by
  rw [approximand, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self, ← IntegrableOn,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ n)]
  apply IntervalIntegrable.continuousOn_mul
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    simpa using (show -1 < s.re - 1 by linarith)
  · fun_prop

private theorem approximand_integral (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    (∫ x in Ioi (0 : ℝ), approximand n s x) = Complex.GammaSeq s n := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn, approximand,
    integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ n),
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]

private theorem strip_bound {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖approximand n s x‖ ≤
      Real.exp (-x) * x ^ (a-1) + Real.exp (-x) * x ^ (b-1) := by
  unfold approximand
  by_cases hn : x ≤ n
  · rw [indicator_of_mem (show x ∈ Ioc 0 (n : ℝ) from ⟨hx, hn⟩),
      norm_mul, Complex.norm_of_nonneg
        (pow_nonneg (sub_nonneg.mpr <| div_le_one_of_le₀ hn (by positivity)) _),
      Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
    have hkernel := Real.one_sub_div_pow_le_exp_neg hn
    have hpow : x ^ (s.re - 1) ≤ x ^ (a-1) + x ^ (b-1) := by
      by_cases h : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
      · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith)).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
    rw [← mul_add]
    exact mul_le_mul hkernel hpow (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  · rw [indicator_of_notMem (fun h => hn h.2), norm_zero]
    positivity

theorem gammaSeq_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn (fun n : ℕ => fun s : ℂ => Complex.GammaSeq s n)
      Complex.Gamma atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  rw [hopen.tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro s hs
  change 0 < s.re at hs
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 s
  have hn : Tendsto (fun p : ℕ × ℂ => p.1) l atTop := tendsto_fst
  have hw : Tendsto (fun p : ℕ × ℂ => p.2) l (𝓝 s) := tendsto_snd
  let a := s.re / 2
  let b := s.re + 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hstrip : ∀ᶠ p : ℕ × ℂ in l, a < p.2.re ∧ p.2.re < b :=
    ((Complex.continuous_re.continuousAt.tendsto.comp hw).eventually
      (Ioo_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)))
  have hlim : Tendsto (fun p : ℕ × ℂ => ∫ x in Ioi (0 : ℝ), approximand p.1 p.2 x)
      l (𝓝 (Complex.Gamma s)) := by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => Real.exp (-x) * x ^ (a-1) + Real.exp (-x) * x ^ (b-1))
    · filter_upwards [hstrip] with p hp using
        (approximand_integrable _ _ (ha.trans hp.1)).aestronglyMeasurable
    · filter_upwards [hstrip] with p hp
      exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun x hx => strip_bound hp.1.le hp.2.le p.1 hx)
    · exact (Real.GammaIntegral_convergent ha).add (Real.GammaIntegral_convergent hb)
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply ae_of_all
      intro x hx
      change 0 < x at hx
      have hkernel : Tendsto (fun n : ℕ => (1 - x / n)^n) atTop (𝓝 (Real.exp (-x))) := by
        simpa only [neg_div, sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-x)
      have hpow : Tendsto (fun p : ℕ × ℂ => (x : ℂ) ^ (p.2-1)) l
          (𝓝 ((x : ℂ) ^ (s-1))) := by
        simp only [Complex.cpow_def_of_ne_zero (show (x : ℂ) ≠ 0 by exact_mod_cast hx.ne')]
        exact Complex.continuous_exp.continuousAt.tendsto.comp
          ((hw.sub tendsto_const_nhds).const_mul _)
      apply ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hkernel.comp hn)).mul hpow).congr'
      filter_upwards [hn.eventually (eventually_ge_atTop ⌈x⌉₊)] with p hp
      rw [approximand, Set.indicator_of_mem (show x ∈ Set.Ioc (0 : ℝ) (p.1 : ℝ) from ⟨hx, Nat.ceil_le.mp hp⟩)] <;> rfl
  have hseq : Tendsto (fun p : ℕ × ℂ => Complex.GammaSeq p.2 p.1) l (𝓝 (Complex.Gamma s)) := hlim.congr' (by
    filter_upwards [hstrip, hn.eventually (eventually_ne_atTop 0)] with p hp hn'
    exact approximand_integral _ hn' _ (ha.trans hp.1))
  have hgamma : ContinuousAt Complex.Gamma s :=
    (Complex.differentiableAt_Gamma s (by
      intro m h
      rw [h] at hs
      simp at hs <;> linarith [Nat.cast_nonneg (α := ℝ) m])).continuousAt
  exact ((hgamma.tendsto.comp hw).prodMk_nhds hseq).mono_right (nhds_le_uniformity _)

end RHConnections.GammaSeqUniform
