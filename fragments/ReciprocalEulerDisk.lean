import Verified
open Metric Set
noncomputable section
namespace RHConnections.ReciprocalLocalComparison
open PerronRamp ZetaDiskLog MertensCriterion ZetaAbelGrowth
theorem euler_reciprocal_bound {s : ℂ} (hs : 1 < s.re) :
    ‖zetaReciprocal s‖ ≤ 2 + 1/(s.re-1) := by
  let b : ℂ := (s.re:ℂ)
  have hb : 1 < b.re := hs
  have hbs : Summable (LSeries.term (1:ℕ → ℂ) b) := LSeriesSummable_one_iff.mpr hb
  have hms : Summable (LSeries.term moebiusCoeff s) := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hterm (n : ℕ) : ‖LSeries.term moebiusCoeff s n‖ ≤ (LSeries.term (1:ℕ → ℂ) b n).re := by
    by_cases hn : n = 0
    · simp [hn]
    rw [LSeries.norm_term_eq,if_neg hn,LSeries.term_of_ne_zero hn]
    have hcoeff : ‖moebiusCoeff n‖ ≤ 1 := by
      rw [moebiusCoeff,Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    change _ ≤ (1 / (n:ℂ)^(s.re:ℂ)).re
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp, ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_le_div_of_nonneg_right hcoeff (by positivity)
  have hbound : ‖zetaReciprocal s‖ ≤ (riemannZeta b).re := by
    rw [zetaReciprocal_eq_moebius_series hs, ← LSeries_one_eq_riemannZeta hb, LSeries, LSeries, Complex.re_tsum hbs]
    exact (norm_tsum_le_tsum_norm hms.norm).trans (hms.norm.tsum_le_tsum hterm ((Complex.hasSum_iff _ _).mp hbs.hasSum).1.summable)
  have hb1 : b ≠ 1 := fun he => by simp [he] at hb
  have hp : 0 < s.re := by linarith
  have h : ‖riemannZeta b‖ ≤ ‖b/(b-1)‖ + ‖b‖/b.re := zeta_vertical_bound hp hb1
  have hdiff : b-1 = ((s.re-1:ℝ):ℂ) := by simp [b]
  rw [norm_div,hdiff] at h
  have hbn : ‖b‖ = s.re := by simp [b,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  rw [hbn,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hs),show b.re = s.re from rfl,div_self hp.ne'] at h
  refine (hbound.trans (Complex.re_le_norm _)).trans (h.trans ?_)
  field_simp [(sub_pos.mpr hs)]
  <;> linarith
end RHConnections.ReciprocalLocalComparison
