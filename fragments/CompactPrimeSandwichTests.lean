import Verified

open Set MeasureTheory Metric
noncomputable section
namespace RHConnections.SmoothedPrimeLimit

def intervalBump (a b δ : ℝ) (hab : a < b) (hδ : 0 < δ) :
    ContDiffBump ((a+b)/2) where
  rIn := (b-a)/2
  rOut := (b-a)/2+δ
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem interval_bump_one {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) {x : ℝ}
    (hx : x ∈ Icc a b) : intervalBump a b δ hab hδ x = 1 := by
  apply (intervalBump a b δ hab hδ).one_of_mem_closedBall
  rw [mem_closedBall,Real.dist_eq,abs_le]
  change -((b-a)/2) ≤ x-(a+b)/2 ∧ x-(a+b)/2 ≤ (b-a)/2
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem interval_bump_zero {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) {x : ℝ}
    (hx : x ∉ Ioo (a-δ) (b+δ)) : intervalBump a b δ hab hδ x = 0 := by
  apply (intervalBump a b δ hab hδ).zero_of_le_dist
  rw [Real.dist_eq]
  change (b-a)/2+δ ≤ |x-(a+b)/2|
  by_contra! h
  rw [abs_lt] at h
  exact hx ⟨by linarith [h.1],by linarith [h.2]⟩

private theorem exp_restrict_integrable {a b : ℝ} :
    Integrable ((Ioc a b).indicator Real.exp) :=
  (Real.continuous_exp.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).integrable_indicator
    measurableSet_Ioc

private theorem exp_restrict_integral {a b : ℝ} (hab : a ≤ b) :
    (∫ x : ℝ, (Ioc a b).indicator Real.exp x) = Real.exp b-Real.exp a := by
  rw [integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le hab,integral_exp]

theorem interval_bump_exp_integral {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    let φ := intervalBump a b δ hab hδ
    Real.exp b-Real.exp a ≤ (∫ x : ℝ, Real.exp x*φ x) ∧
      (∫ x : ℝ, Real.exp x*φ x) ≤ Real.exp (b+δ)-Real.exp (a-δ) := by
  let φ := intervalBump a b δ hab hδ
  have hi : Integrable (fun x : ℝ => Real.exp x*φ x) :=
    (Real.continuous_exp.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  constructor
  · rw [← exp_restrict_integral hab.le]
    refine integral_mono exp_restrict_integrable hi (fun x => ?_)
    by_cases hx : x ∈ Ioc a b
    · rw [indicator_of_mem hx,interval_bump_one hab hδ ⟨hx.1.le,hx.2⟩,mul_one]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (Real.exp_pos _).le (φ.nonneg' x)
  · rw [← exp_restrict_integral (show a-δ ≤ b+δ by linarith)]
    refine integral_mono hi exp_restrict_integrable (fun x => ?_)
    by_cases hx : x ∈ Ioc (a-δ) (b+δ)
    · rw [indicator_of_mem hx]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (φ.le_one (x := x)) (Real.exp_pos x).le
    · rw [indicator_of_notMem hx,interval_bump_zero hab hδ (fun h => hx ⟨h.1,h.2.le⟩),mul_zero]

end RHConnections.SmoothedPrimeLimit
