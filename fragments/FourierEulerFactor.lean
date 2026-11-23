import Verified

noncomputable section
namespace RHConnections.ArithmeticFourierInversion
open scoped LSeries.notation
open MertensCriterion PerronRamp ZetaDiskLog

def fourierEulerFactor (B : ℕ) (s : ℂ) := LSeries (fun n => (g B n : ℂ)) s
def fourierInverseFactor (B : ℕ) (s : ℂ) := LSeries (fun n => (h B n : ℂ)) s

private theorem abscissa_le_zero_of_inverse_majorant {u : ArithmeticFunction ℝ}
    (hu : ∀ k, |u k|≤1/(k:ℝ)) :
    LSeries.abscissaOfAbsConv (fun k => (u k:ℂ)) ≤ 0 := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := fun k => (u k:ℂ)) (x := -1) (by
      refine ⟨1,fun k _ => ?_⟩
      simpa [Complex.norm_real,Real.norm_eq_abs,Real.rpow_neg_one,one_div] using hu k)
  convert h using 1
  norm_cast

private theorem absConv_lt {u : ArithmeticFunction ℝ}
    (hu : ∀ k, |u k|≤1/(k:ℝ)) {s : ℂ} (hs : 0<s.re) :
    LSeries.abscissaOfAbsConv (fun k => (u k:ℂ)) < s.re :=
  (abscissa_le_zero_of_inverse_majorant hu).trans_lt (by exact_mod_cast hs)

theorem fourierEulerFactor_summable (B : ℕ) {s : ℂ} (hs : 0<s.re) :
    LSeriesSummable (fun n => (g B n:ℂ)) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re (absConv_lt (abs_g_le B) hs)

theorem fourierInverseFactor_summable (B : ℕ) {s : ℂ} (hs : 0<s.re) :
    LSeriesSummable (fun n => (h B n:ℂ)) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re (absConv_lt (abs_h_le B) hs)

theorem fourierEulerFactor_analytic (B : ℕ) :
    AnalyticOnNhd ℂ (fourierEulerFactor B) {s : ℂ | 0<s.re} :=
  fun _ hs => LSeries_analyticOnNhd _ _ (absConv_lt (abs_g_le B) hs)

theorem fourierInverseFactor_analytic (B : ℕ) :
    AnalyticOnNhd ℂ (fourierInverseFactor B) {s : ℂ | 0<s.re} :=
  fun _ hs => LSeries_analyticOnNhd _ _ (absConv_lt (abs_h_le B) hs)

private theorem complex_convolution (u v : ArithmeticFunction ℝ) :
    LSeries.convolution (fun n => (u n:ℂ)) (fun n => (v n:ℂ)) =
    fun n => ((u*v) n:ℂ) := by
  funext n
  simp [LSeries.convolution_def,ArithmeticFunction.mul_apply]

theorem fourierEulerFactor_mul_inverse (B : ℕ) {s : ℂ} (hs : 0<s.re) :
    fourierEulerFactor B s * fourierInverseFactor B s = 1 := by
  unfold fourierEulerFactor fourierInverseFactor
  rw [←LSeries_convolution' (fourierEulerFactor_summable B hs) (fourierInverseFactor_summable B hs),
    complex_convolution,g_convolution_h]
  have hunit : (fun n => ((1:ArithmeticFunction ℝ) n:ℂ))=LSeries.delta := by
    funext n
    by_cases hn : n=1 <;> simp [LSeries.delta,hn]
  rw [hunit,LSeries_delta]
  rfl

theorem fourierEulerFactor_ne_zero (B : ℕ) {s : ℂ} (hs : 0<s.re) :
    fourierEulerFactor B s ≠ 0 :=
  left_ne_zero_of_mul ((fourierEulerFactor_mul_inverse B hs).trans_ne one_ne_zero)

private theorem muR_complex : (fun n => (muR n : ℂ))=moebiusCoeff := by
  funext n
  simp [muR,moebiusCoeff]

theorem scalar_LSeries_summable (B : ℕ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (fun n => ((g B * muR) n:ℂ)) s := by
  rw [←complex_convolution,muR_complex]
  exact (fourierEulerFactor_summable B (zero_lt_one.trans hs)).convolution
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

theorem scalar_LSeries_eq_factor (B : ℕ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => ((g B * muR) n:ℂ)) s = fourierEulerFactor B s * zetaReciprocal s := by
  rw [←complex_convolution,muR_complex,zetaReciprocal_eq_moebius_series hs]
  exact LSeries_convolution' (fourierEulerFactor_summable B (zero_lt_one.trans hs))
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

end RHConnections.ArithmeticFourierInversion
