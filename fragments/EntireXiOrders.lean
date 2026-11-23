import Verified

open Filter
noncomputable section
namespace RHConnections.SpectralTail

def entireXi (s : ℂ) : ℂ := s*(s-1)*completedRiemannZeta₀ s + 1

theorem entireXi_analytic (s : ℂ) : AnalyticAt ℂ entireXi s := by
  exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
    (differentiable_completedZeta₀.analyticAt s)).add analyticAt_const

theorem entireXi_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    entireXi s = s*(s-1)*completedRiemannZeta s := by
  unfold entireXi
  rw [completedRiemannZeta_eq]
  have h : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp [h0, sub_ne_zero.mpr h1, h]
  <;> ring

theorem gamma_real_nonzero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℝ s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have hh := congrArg Complex.re hn
  norm_num [Complex.mul_re, Complex.neg_re] at hh
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gamma_real_analytic_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  have hU : IsOpen {t : ℂ | 0 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ (fun t : ℂ => Complex.Gamma (t/2)) {t : ℂ | 0 < t.re} := by
    intro t ht
    have hn (n : ℕ) : t/2 ≠ -(n : ℂ) := by
      intro h
      have hh := congrArg Complex.re h
      norm_num [Complex.div_re, Complex.neg_re] at hh
      exact (not_le_of_gt (show 0 < t.re from ht)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ((Complex.differentiableAt_Gamma _ hn).comp t
      (differentiableAt_id.div_const (2:ℂ))).differentiableWithinAt
  have hG' : AnalyticAt ℂ (fun t : ℂ => Complex.Gamma (t/2)) s :=
    hG.analyticOnNhd hU s hs
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP : AnalyticAt ℂ (fun t : ℂ => Complex.exp
      (Complex.log (Real.pi : ℂ)*(-t/2))) s := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => -t/2) s := analyticAt_id.neg.div_const
    exact (analyticAt_const.mul hlin).cexp'
  change AnalyticAt ℂ (fun t : ℂ => (Real.pi : ℂ)^(-t/2) * Complex.Gamma (t/2)) s
  simp_rw [Complex.cpow_def_of_ne_zero hp]
  exact hP.mul hG'

theorem entireXi_zeta_germ {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    entireXi =ᶠ[nhds s] (fun t => (t*(t-1)*Complex.Gammaℝ t)*riemannZeta t) := by
  have hnear : {t : ℂ | 0 < t.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hnear, eventually_ne_nhds h1] with t ht ht1
  have ht0 : t ≠ 0 := by
    intro he
    change 0 < t.re at ht
    simpa [he] using ht
  have hG := gamma_real_nonzero_of_re_pos ht
  rw [entireXi_completed ht0 ht1, riemannZeta_def_of_ne_zero ht0]
  field_simp
  <;> ring

theorem entireXi_order_eq_zeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt entireXi s = analyticOrderAt riemannZeta s := by
  have hs0 : s ≠ 0 := by intro he; simpa [he] using hs
  have hK : AnalyticAt ℂ (fun t => t*(t-1)*Complex.Gammaℝ t) s :=
    (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul (gamma_real_analytic_of_re_pos hs)
  have hn : (fun t => t*(t-1)*Complex.Gammaℝ t) s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr h1)) (gamma_real_nonzero_of_re_pos hs)
  have he := analyticOrderAt_congr (entireXi_zeta_germ hs h1)
  have hm := analyticOrderAt_mul hK (analyticOn_riemannZeta s h1)
  change analyticOrderAt (fun t => (t*(t-1)*Complex.Gammaℝ t)*riemannZeta t) s =
    _ at hm
  have hk0 : analyticOrderAt (fun t : ℂ => t*(t-1)*Complex.Gammaℝ t) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hn)
  rw [he, hm, hk0, zero_add]

theorem entireXi_two_ne_zero : entireXi 2 ≠ 0 := by
  have h := (entireXi_zeta_germ (s := 2) (by norm_num) (by norm_num)).eq_of_nhds
  rw [h]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (gamma_real_nonzero_of_re_pos (by norm_num)))
    (riemannZeta_ne_zero_of_one_le_re (by norm_num))

end RHConnections.SpectralTail
