import Verified

open MeasureTheory Set
noncomputable section
namespace RHConnections.RieszPrimeMellin
open PrimeErrorLaplace

def rieszError (x : ℝ) : ℝ := x⁻¹ * ∫ t in Set.Ioc (1 : ℝ) x, realPrimeError t

theorem rieszError_measurable : Measurable rieszError := by
  let D := {p : ℝ × ℝ | 1 < p.2 ∧ p.2 ≤ p.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)
  have hm := ((real_prime_error_measurable.comp measurable_snd).indicator hD).stronglyMeasurable
  have h := (hm.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hi (x : ℝ) : (∫ t : ℝ, D.indicator (fun p => realPrimeError p.2) (x,t)) =
      ∫ t in Ioc 1 x, realPrimeError t := by
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  change Measurable (fun x : ℝ => ∫ t : ℝ, D.indicator (fun p => realPrimeError p.2) (x,t)) at h
  simp_rw [hi] at h
  exact measurable_id.inv.mul h

private def kernel (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  if p.1 < p.2 then (realPrimeError p.1 : ℂ) * (p.2 : ℂ) ^ (-(s+2)) else 0

private theorem tail_measure {t : ℝ} (ht : 1 < t) :
    ((volume : Measure ℝ).restrict (Ioi 1)).restrict (Ioi t) = volume.restrict (Ioi t) := by
  rw [Measure.restrict_restrict measurableSet_Ioi,Ioi_inter_Ioi,max_eq_left ht.le]

private theorem kernel_tail (s : ℂ) {t : ℝ} (ht : 1 < t) :
    (∫ x in Ioi (1 : ℝ), kernel s (t,x)) =
    (realPrimeError t : ℂ) * (∫ x in Ioi t, (x : ℂ) ^ (-(s+2))) := by
  change (∫ x in Ioi (1 : ℝ), (Ioi t).indicator
    (fun x => (realPrimeError t : ℂ) * (x : ℂ) ^ (-(s+2))) x) = _
  rw [integral_indicator measurableSet_Ioi,tail_measure ht,integral_const_mul]

private theorem kernel_head (s : ℂ) {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi (1 : ℝ), kernel s (t,x)) = (rieszError x : ℂ) * (x : ℂ)^(-(s+1)) := by
  change (∫ t in Ioi (1 : ℝ), (Iio x).indicator
    (fun t => (realPrimeError t : ℂ) * (x : ℂ) ^ (-(s+2))) t) = _
  rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
    inter_comm,Ioi_inter_Iio,← integral_Ioc_eq_integral_Ioo,integral_mul_const,integral_complex_ofReal]
  have hxn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he : (x:ℂ)^(-(s+2)) = (x:ℂ)⁻¹ * (x:ℂ)^(-(s+1)) := by
    rw [show -(s+2) = -1 + -(s+1) by ring,Complex.cpow_add _ _ hxn,Complex.cpow_neg_one]
  rw [he,rieszError,Complex.ofReal_mul,Complex.ofReal_inv]
  ring

private theorem kernel_integrable {s : ℂ} (hs : 1 < s.re) :
    Integrable (kernel s) ((volume.restrict (Ioi (1:ℝ))).prod (volume.restrict (Ioi (1:ℝ)))) := by
  have hq : (-(s+2)).re < -1 := by simp; linarith
  have hm : Measurable (kernel s) := by
    unfold kernel
    apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
    · apply Measurable.mul (Complex.measurable_ofReal.comp (real_prime_error_measurable.comp measurable_fst))
      fun_prop
    · exact measurable_const
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change Integrable ((Ioi t).indicator (fun x : ℝ => (realPrimeError t : ℂ) * (x : ℂ)^(-(s+2)))) _
    rw [integrable_indicator_iff measurableSet_Ioi,IntegrableOn,tail_measure ht]
    exact (integrableOn_Ioi_cpow_of_lt hq (lt_trans (by norm_num) ht)).const_mul _
  · apply ((prime_error_weighted_integrable hs).norm.div_const (s.re+1)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    have he (x : ℝ) : ‖kernel s (t,x)‖ = (Ioi t).indicator
        (fun x : ℝ => ‖(realPrimeError t:ℂ)‖ * ‖(x:ℂ)^(-(s+2))‖) x := by
      by_cases h : t < x <;> simp [kernel,Set.indicator,Set.mem_Ioi,h]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioi,tail_measure ht,integral_const_mul]
    have hc : (∫ x in Ioi t, ‖(x:ℂ)^(-(s+2))‖) = ∫ x in Ioi t, x ^ (-(s.re+2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans ht0 hx)]
      simp
    rw [hc,integral_Ioi_rpow_of_lt (by linarith) ht0]
    change ‖(realPrimeError t : ℂ) * (t : ℂ)^(-(s+1))‖ / (s.re+1) = _
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.neg_re,Complex.add_re,Complex.one_re]
    rw [show -(s.re+2)+1 = -(s.re+1) by ring]
    rw [div_neg,neg_div,neg_neg]
    ring

theorem riesz_error_mellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (rieszError x:ℂ)*(x:ℂ)^(-(s+1))) (Ioi 1) ∧
    (∫ x in Ioi (1:ℝ), (rieszError x:ℂ)*(x:ℂ)^(-(s+1))) =
      (∫ x in Ioi (1:ℝ), (realPrimeError x:ℂ)*(x:ℂ)^(-(s+1)))/(s+1) := by
  have hK := kernel_integrable hs
  have hh : (fun x : ℝ => ∫ t in Ioi (1:ℝ), kernel s (t,x)) =ᵐ[volume.restrict (Ioi 1)]
      (fun x : ℝ => (rieszError x:ℂ)*(x:ℂ)^(-(s+1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using kernel_head s hx
  refine ⟨hK.integral_prod_right.congr hh, ?_⟩
  rw [← integral_congr_ae hh, ← integral_integral_swap (f := fun t x => kernel s (t,x)) hK,
    ← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [kernel_tail s ht,integral_Ioi_cpow_of_lt (by simp; linarith) (lt_trans (by norm_num) ht)]
  rw [show -(s+2)+1 = -(s+1) by ring]
  rw [div_neg,neg_div,neg_neg]
  ring

end RHConnections.RieszPrimeMellin
