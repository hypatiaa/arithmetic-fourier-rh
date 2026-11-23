import Verified

noncomputable section
namespace RHConnections.ZetaZeroFreeRegion
open ChebyshevCriterion PerronRampBounds

def zetaSlope (s : ℂ) : ℂ := -deriv riemannZeta s / riemannZeta s

private theorem vertical_re (σ t : ℝ) : (vertical σ t).re = σ := by
  simp [vertical,Complex.add_re,Complex.mul_re]

private theorem lseries_term_real (σ t : ℝ) (n : ℕ) :
    (LSeries.term mangoldtCoeff (vertical σ t) n).re =
      ArithmeticFunction.vonMangoldt n * Real.exp (-(σ*Real.log n)) *
        Real.cos (t*Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC,
    ← Complex.natCast_log,div_eq_mul_inv,← Complex.exp_neg]
  simp only [mangoldtCoeff,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.exp_re,Complex.neg_re,Complex.neg_im,vertical,Complex.add_re,Complex.add_im,
    Complex.mul_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add,Real.cos_neg]
  rw [mul_comm (Real.log n) σ,mul_comm (Real.log n) t]
  ring

private theorem von_mangoldt_real_hasSum (σ t : ℝ) (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (LSeries.term mangoldtCoeff (vertical σ t) n).re)
      (zetaSlope (vertical σ t)).re := by
  have hs : 1 < (vertical σ t).re := by rwa [vertical_re]
  have h : HasSum (LSeries.term mangoldtCoeff (vertical σ t)) (LSeries mangoldtCoeff (vertical σ t)) :=
    (show Summable (LSeries.term mangoldtCoeff (vertical σ t)) from
      ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  have he : LSeries mangoldtCoeff (vertical σ t) = zetaSlope (vertical σ t) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [he] at h
  exact Complex.hasSum_re h

theorem zeta_three_point_positivity (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3*(zetaSlope (vertical σ 0)).re +
      4*(zetaSlope (vertical σ t)).re + (zetaSlope (vertical σ (2*t))).re := by
  have h := (((von_mangoldt_real_hasSum σ 0 hσ).mul_left 3).add
    ((von_mangoldt_real_hasSum σ t hσ).mul_left 4)).add (von_mangoldt_real_hasSum σ (2*t) hσ)
  rw [← h.tsum_eq]
  apply tsum_nonneg
  intro n
  simp only [lseries_term_real,zero_mul,Real.cos_zero,mul_one]
  rw [show 2*t*Real.log n = 2*(t*Real.log n) by ring,Real.cos_two_mul]
  have hweight : 0 ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-(σ*Real.log n)) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  nlinarith only [mul_nonneg hweight (sq_nonneg (1+Real.cos (t*Real.log n)))]

end RHConnections.ZetaZeroFreeRegion
