import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
noncomputable section
namespace RHConnections.WeightedBulk

def positiveFormula (j : ℕ) (z z₀ : ℂ) (y : ℝ) : ℂ :=
  (-z)^j * Complex.exp (-z*(y : ℂ)) - (-z₀)^j * Complex.exp (-z₀*(y : ℂ))

def bulk (j : ℕ) (z z₀ : ℂ) (y : ℝ) : ℂ :=
  if 0 < y then positiveFormula j z z₀ y else 0

theorem positiveFormula_bound (j : ℕ) (z z₀ : ℂ) {beta y : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hy : 0 ≤ y) :
    ‖positiveFormula j z z₀ y‖ ≤ (‖z‖^j+‖z₀‖^j)*Real.exp (-beta*y) := by
  have h1 : ‖Complex.exp (-z*(y : ℂ))‖ ≤ Real.exp (-beta*y) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  have h2 : ‖Complex.exp (-z₀*(y : ℂ))‖ ≤ Real.exp (-beta*y) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  calc
    _ ≤ ‖(-z)^j*Complex.exp (-z*(y : ℂ))‖ +
        ‖(-z₀)^j*Complex.exp (-z₀*(y : ℂ))‖ := norm_sub_le _ _
    _ = ‖z‖^j*‖Complex.exp (-z*(y : ℂ))‖+
        ‖z₀‖^j*‖Complex.exp (-z₀*(y : ℂ))‖ := by simp only [norm_mul, norm_pow, norm_neg]
    _ ≤ ‖z‖^j*Real.exp (-beta*y)+‖z₀‖^j*Real.exp (-beta*y) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by ring

theorem weighted_pointwise_bound (j : ℕ) (z z₀ : ℂ) (sigma : ℝ) {beta y : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hy : 0 ≤ y) :
    Real.exp (sigma*y)*‖positiveFormula j z z₀ y‖ ≤
      (‖z‖^j+‖z₀‖^j)*Real.exp ((sigma-beta)*y) := by
  calc
    _ ≤ Real.exp (sigma*y)*((‖z‖^j+‖z₀‖^j)*Real.exp (-beta*y)) :=
      mul_le_mul_of_nonneg_left (positiveFormula_bound j z z₀ hz hz₀ hy) (Real.exp_pos _).le
    _ = _ := by
      rw [show (sigma-beta)*y = sigma*y + -beta*y by ring, Real.exp_add]
      ring

theorem weighted_integrableOn (j : ℕ) (z z₀ : ℂ) {sigma beta : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hs : sigma < beta) :
    IntegrableOn (fun y : ℝ => Real.exp (sigma*y)*‖positiveFormula j z z₀ y‖) (Ioi 0) := by
  have hm : IntegrableOn (fun y : ℝ =>
      (‖z‖^j+‖z₀‖^j)*Real.exp ((sigma-beta)*y)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : sigma-beta < 0) 0).const_mul _
  have hc : Continuous (fun y : ℝ => Real.exp (sigma*y)*‖positiveFormula j z z₀ y‖) := by
    unfold positiveFormula
    fun_prop
  apply hm.mono' hc.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    using weighted_pointwise_bound j z z₀ sigma hz hz₀ hy.le

theorem weighted_massOn_bound (j : ℕ) (z z₀ : ℂ) {sigma beta : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hs : sigma < beta) :
    (∫ y : ℝ in Ioi 0, Real.exp (sigma*y)*‖positiveFormula j z z₀ y‖) ≤
      (‖z‖^j+‖z₀‖^j)/(beta-sigma) := by
  have hf := weighted_integrableOn j z z₀ hz hz₀ hs
  have hm : IntegrableOn (fun y : ℝ =>
      (‖z‖^j+‖z₀‖^j)*Real.exp ((sigma-beta)*y)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : sigma-beta < 0) 0).const_mul _
  calc
    _ ≤ ∫ y : ℝ in Ioi 0, (‖z‖^j+‖z₀‖^j)*Real.exp ((sigma-beta)*y) := by
      apply integral_mono_ae hf hm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact weighted_pointwise_bound j z z₀ sigma hz hz₀ hy.le
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : sigma-beta < 0) 0]
      simp only [mul_zero, Real.exp_zero]
      rw [show sigma-beta = -(beta-sigma) by ring]
      simp only [div_eq_mul_inv, inv_neg, neg_mul_neg, one_mul]

theorem weighted_bulk_indicator (j : ℕ) (z z₀ : ℂ) (sigma : ℝ) :
    (fun y : ℝ => Real.exp (sigma*y)*‖bulk j z z₀ y‖) =
      (Set.Ioi (0:ℝ)).indicator (fun y : ℝ => Real.exp (sigma*y)*‖positiveFormula j z z₀ y‖) := by
  funext y
  by_cases hy : 0 < y <;> simp [bulk, Set.indicator, hy]

theorem weighted_bulk_integrable (j : ℕ) (z z₀ : ℂ) {sigma beta : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hs : sigma < beta) :
    Integrable (fun y : ℝ => Real.exp (sigma*y)*‖bulk j z z₀ y‖) := by
  rw [weighted_bulk_indicator]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr (weighted_integrableOn j z z₀ hz hz₀ hs)

theorem weighted_bulk_mass_bound (j : ℕ) (z z₀ : ℂ) {sigma beta : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hs : sigma < beta) :
    (∫ y : ℝ, Real.exp (sigma*y)*‖bulk j z z₀ y‖) ≤
      (‖z‖^j+‖z₀‖^j)/(beta-sigma) := by
  rw [weighted_bulk_indicator, integral_indicator measurableSet_Ioi]
  exact weighted_massOn_bound j z z₀ hz hz₀ hs

theorem weighted_bulk_uniform (j : ℕ) (z z₀ : ℂ) {sigma beta a L : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hgap : a < beta)
    (hsigma : |sigma| ≤ a) (hLz : ‖z‖ ≤ L) (hLz₀ : ‖z₀‖ ≤ L) :
    (∫ y : ℝ, Real.exp (sigma*y)*‖bulk j z z₀ y‖) ≤ 2*L^j/(beta-a) := by
  have hL : 0 ≤ L := (norm_nonneg z).trans hLz
  have hs : sigma ≤ a := (le_abs_self sigma).trans hsigma
  have hnum : ‖z‖^j+‖z₀‖^j ≤ 2*L^j := by
    have h1 := pow_le_pow_left₀ (norm_nonneg z) hLz j
    have h2 := pow_le_pow_left₀ (norm_nonneg z₀) hLz₀ j
    linarith
  calc
    _ ≤ (‖z‖^j+‖z₀‖^j)/(beta-sigma) :=
      weighted_bulk_mass_bound j z z₀ hz hz₀ (lt_of_le_of_lt hs hgap)
    _ ≤ 2*L^j/(beta-sigma) := div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ 2*L^j/(beta-a) := div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

#print axioms positiveFormula_bound
#print axioms weighted_pointwise_bound
#print axioms weighted_integrableOn
#print axioms weighted_massOn_bound
#print axioms weighted_bulk_indicator
#print axioms weighted_bulk_integrable
#print axioms weighted_bulk_mass_bound
#print axioms weighted_bulk_uniform
end RHConnections.WeightedBulk
