import Verified
import Mathlib.Analysis.Complex.JensenFormula

noncomputable section
namespace RHConnections.CanonicalFactor
open SpectralTail AffineFromRealPart Metric Filter MeromorphicOn Real

theorem circleAverage_log_norm_nonneg_of_one {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {R : ℝ} (hR : 0 < R) :
    0 ≤ circleAverage (fun s => Real.log ‖f s‖) 0 R := by
  have ha : AnalyticOnNhd ℂ f (closedBall (0:ℂ) |R|) := fun s _ => hf s
  rw [ha.circleAverage_log_norm hR.ne' (h0.trans_ne one_ne_zero), h0, norm_one,
    Real.log_one, add_zero]
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall (0:ℂ) |R|
  · apply mul_nonneg (by exact_mod_cast ha.divisor_nonneg u)
    by_cases hu0 : u = 0
    · simp [hu0]
    · simp only [zero_sub, norm_neg]
      rw [← div_eq_mul_inv]
      apply Real.log_nonneg
      apply (one_le_div (norm_pos_iff.mpr hu0)).mpr
      simpa [abs_of_pos hR, mem_closedBall, dist_zero_right] using hu
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

theorem quotient_meanAbsRe_le {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (he : ∀ s, Complex.exp (G s) = xiProductQuotient s)
    {R A B : ℝ} (hR : 0 < R)
    (hx : ∀ s ∈ sphere (0:ℂ) R, Real.log ‖entireXi s‖ ≤ A)
    (hp : ∀ s ∈ sphere (0:ℂ) R, Real.log ‖zetaCanonicalProduct s‖ ≤ B) :
    meanAbsRe G R ≤ 2 * max A B := by
  classical
  let X := fun s : ℂ => Real.log ‖entireXi s‖
  let P := fun s : ℂ => Real.log ‖zetaCanonicalProduct s‖
  let U := fun s : ℂ => |(G s).re|
  let F := U+X+P
  let H := fun s : ℂ => if zetaCanonicalProduct s = 0 then 2*max A B else F s
  have hP0 : zetaCanonicalProduct 0 = 1 := by simp [zetaCanonicalProduct,zetaFactor,genusOne]
  have hX0 : entireXi 0 = 1 := by simp [entireXi]
  have hX : 0 ≤ circleAverage X 0 R := circleAverage_log_norm_nonneg_of_one entireXi_analytic hX0 hR
  have hP : 0 ≤ circleAverage P 0 R := circleAverage_log_norm_nonneg_of_one
    (fun z => zetaCanonicalProduct_entire z (Set.mem_univ _)) hP0 hR
  have iU : CircleIntegrable U 0 R := ContinuousOn.circleIntegrable hR.le (Complex.continuous_re.comp hG.continuous).abs.continuousOn
  have iX : CircleIntegrable X 0 R := MeromorphicOn.circleIntegrable_log_norm
    (fun z _ => (entireXi_analytic z).meromorphicAt)
  have iP : CircleIntegrable P 0 R := MeromorphicOn.circleIntegrable_log_norm
    (fun z _ => (zetaCanonicalProduct_entire z (Set.mem_univ _)).meromorphicAt)
  have hne : ∀ᶠ z in codiscreteWithin (sphere (0:ℂ) |R|), zetaCanonicalProduct z ≠ 0 :=
    codiscreteWithin_mono (Set.subset_univ _) (zetaCanonicalProduct_entire.preimage_zero_mem_codiscreteWithin
      (hP0.trans_ne one_ne_zero) (Set.mem_univ _) isConnected_univ)
  have hFH : F =ᶠ[codiscreteWithin (sphere (0:ℂ) |R|)] H := by
    filter_upwards [hne] with z hz
    simp [H,hz]
  have hMean : circleAverage F 0 R ≤ 2*max A B := by
    rw [circleAverage_congr_codiscreteWithin hFH hR.ne']
    apply circleAverage_mono_on_of_le_circle (CircleIntegrable.congr_codiscreteWithin hFH ((iU.add iX).add iP))
    intro s hs
    have hs' : s ∈ sphere (0:ℂ) R := by simpa [abs_of_pos hR] using hs
    by_cases hz : zetaCanonicalProduct s = 0
    · simp [H,hz]
    · simp only [H, if_neg hz]
      have heq : X s = (G s).re + P s := by
        dsimp [X,P]
        rw [← xiProductQuotient_mul s, ← he, norm_mul, Complex.norm_exp,
          Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr hz), Real.log_exp]
      have hXX : X s ≤ max A B := (hx s hs').trans (le_max_left _ _)
      have hPP : P s ≤ max A B := (hp s hs').trans (le_max_right _ _)
      change |(G s).re| + X s + P s ≤ _
      rcases le_total 0 (G s).re with h|h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
  change circleAverage (U+X+P) 0 R ≤ _ at hMean
  rw [circleAverage_add (iU.add iX) iP, circleAverage_add iU iX] at hMean
  change circleAverage U 0 R ≤ _
  linarith

end RHConnections.CanonicalFactor
