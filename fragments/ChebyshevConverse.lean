import Verified

open MeasureTheory Filter Asymptotics Set
noncomputable section
namespace RHConnections.ChebyshevCriterion
open PerronRamp PoleCompensation ZetaDiskLog PerronGrowthTransfer

private theorem mangoldt_integrand_integrable {X h : ℝ} (hX : 0 < X) (hh : 0 < h) :
    Integrable (fun v : ℝ => lseriesPerronIntegrand mangoldtCoeff h X (probe 2 v)) := by
  let B := ∑' n : ℕ, ‖LSeries.term mangoldtCoeff (2:ℂ) n‖
  have hK := kernel_integrable (c := 2) hh (by norm_num)
  apply (hK.norm.const_mul (B*X^2)).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro v
    let s := probe 2 v
    have hs : 1 < s.re := by rw [show s.re = 2 from probe_re 2 v]; norm_num
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    have hs1 : s ≠ 1 := fun he => by simp [he] at hs
    have hls : LSeries mangoldtCoeff =ᶠ[nhds s] fun z => -deriv riemannZeta z / riemannZeta z := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz'
      exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz'
    have hzA := analyticOn_riemannZeta s hs1
    have hL := (hzA.deriv.neg.div hzA hz).congr hls.symm
    have hA := integrand_analytic (G := LSeries mangoldtCoeff) (by linarith) hL hh hX
    have hP : ContinuousAt (probe 2) v := by unfold probe; fun_prop
    exact ContinuousAt.comp (f := probe 2) (g := integrand (LSeries mangoldtCoeff) h X) hA.continuousAt hP
  · exact ae_of_all _ fun v => by
      let s := probe 2 v
      have hRe : s.re = 2 := probe_re 2 v
      have hs : (1:ℝ) < s.re := by rw [hRe]; norm_num
      have hsum := (show Summable (LSeries.term mangoldtCoeff s) from
        ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
      have hB : ‖LSeries mangoldtCoeff s‖ ≤ B := by
        unfold LSeries
        refine (norm_tsum_le_tsum_norm hsum).trans_eq ?_
        apply tsum_congr
        intro n
        rw [LSeries.norm_term_eq,LSeries.norm_term_eq,hRe]
        norm_num
      change ‖LSeries mangoldtCoeff s*(X:ℂ)^s*kernel h s‖ ≤ _
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hRe, Real.rpow_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (by positivity)) (norm_nonneg _)

theorem smoothed_chebyshev_compensated_euler {X h : ℝ} (hX : 0 < X) (hh : 0 < h) :
    smoothedChebyshev h X - (smoothedPole h X : ℂ) =
      ∫ v : ℝ, integrand regularizedLogDerivative h X (probe 2 v) := by
  have ha : LSeriesSummable mangoldtCoeff (2:ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have h0 : mangoldtCoeff 0 = 0 := by simp [mangoldtCoeff]
  have hM := smoothedLSeries_eq_euler_integral mangoldtCoeff h0 hh (by norm_num : (0:ℝ)<2) hX ha
  have hP := smoothedPole_euler_pairing hh hX
  change smoothedLSeries mangoldtCoeff h X - _ = _
  rw [hM,hP.2,← integral_sub (mangoldt_integrand_integrable hX hh) hP.1]
  apply integral_congr_ae
  exact ae_of_all _ fun v => by
    let s := probe 2 v
    have hRe : s.re = 2 := probe_re 2 v
    have hs : 1 < s.re := by rw [hRe]; norm_num
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    have hs1 : s ≠ 1 := fun he => by simp [he] at hs
    change lseriesPerronIntegrand mangoldtCoeff h X s -
      (s-1)⁻¹*(X:ℂ)^s*kernel h s = integrand regularizedLogDerivative h X s
    have hL : LSeries mangoldtCoeff s = -deriv riemannZeta s / riemannZeta s :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    rw [integrand,regularizedLogDerivative_eq hs1 hz,compensatedLogDerivative,lseriesPerronIntegrand,hL]
    simp only [one_div]
    ring

theorem chebyshev_cancellation_of_RH (hRH : RiemannHypothesis) : ChebyshevCancellation := by
  apply chebyshev_cancellation_of_smoothed_power (P := fun h X => (smoothedPole h X : ℂ))
  · intro X h hX hh hh1
    rw [← Complex.ofReal_one,← Complex.ofReal_sub]
    simpa only [Complex.ofReal_sub] using
      (show ‖((smoothedPole h X - (X-1):ℝ):ℂ)‖ ≤ 3*X*h by
        rw [Complex.norm_real,Real.norm_eq_abs]
        exact smoothedPole_error hX hh hh1)
  · intro d hd hd1
    let b : ℝ := 1/2+d
    have hb : 1/2 < b := by dsimp [b]; linarith
    have hb1 : b < 1 := by dsimp [b]; linarith
    obtain ⟨D,hD,hBound⟩ := regularizedLogDerivative_subpower_of_RH hRH hb hb1 hd
    have hA : AnalyticOnNhd ℂ regularizedLogDerivative {s : ℂ | s.re ∈ Icc b 2} :=
      fun s hs => regularizedLogDerivative_on_halfplane (right_zero_free_of_RH hRH) s
        (hb.trans_le hs.1)
    obtain ⟨C,hC,h⟩ := euler_integral_bound_of_strip_growth (by linarith : 0 < b)
      (by linarith : b ≤ 2) hd (by linarith : d < 1) hD hA
      (fun s hs => hBound s hs.1 hs.2)
    refine ⟨C,hC,?_⟩
    intro X h' hX hh hh1
    rw [smoothed_chebyshev_compensated_euler (by linarith : 0 < X) hh]
    exact h X h' hX hh hh1

theorem chebyshev_cancellation_iff_RH : ChebyshevCancellation ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_chebyshev,chebyshev_cancellation_of_RH⟩

theorem chebyshev_cancellation_iff_line_residual {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    ChebyshevCancellation ↔ ZetaLineEulerResidual z₀ :=
  chebyshev_cancellation_iff_RH.trans (riemannHypothesis_iff_line_euler_residual hz₀)

end RHConnections.ChebyshevCriterion
