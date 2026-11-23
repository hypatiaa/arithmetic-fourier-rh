import Verified
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace RHConnections.SpectralTail
open FourierDecay WeightedConvolution RelativeResolvent AnalyticObligations

theorem relative_spectral_analytic {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (C : ℝ)
    (hcount : ∀ (j : ℕ) (s : Finset ι), (∀ i ∈ s, |(xi i).im| < (2 : ℝ)^(j+1)) →
      (∑ i ∈ s, (mult i : ℝ)) ≤ C * ((j : ℝ)+1) * 2^j)
    {a : ℝ} (ha : 0 ≤ a) (hstrip : ∀ i, |(xi i).re| ≤ a)
    {z₀ : ℂ} (hz₀ : a < z₀.re) :
    AnalyticOnNhd ℂ (fun z => ∑' i, (mult i : ℂ)*relative z z₀ (xi i)) (halfPlane a) := by
  have hU : IsOpen (halfPlane a) := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  let K := Metric.closedBall z (r/2)
  have hK : K ⊆ halfPlane a := fun w hw => hrU (Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith)))
  obtain ⟨D, hD, hbound⟩ := fullCandidate_weighted_angular_decay ha hz₀ K
    (isCompact_closedBall _ _) hK
  let V := Metric.ball z (r/2)
  have hsub : V ⊆ K := Metric.ball_subset_closedBall
  let F := fun i w => (mult i : ℂ)*relative w z₀ (xi i)
  let M := fun i => D*((mult i : ℝ)/(1+(xi i).im^2))
  have hM : Summable M := (multiplicity_majorant_summable (fun i => (xi i).im) mult C hcount).mul_left D
  have hre (i : ι) : (xi i).re ≤ a := (le_abs_self _).trans (hstrip i)
  have hd (i : ι) : DifferentiableOn ℂ (F i) V := by
    have hinv : DifferentiableOn ℂ (fun w : ℂ => (w-xi i)⁻¹) V :=
      (differentiableOn_id.sub_const _).inv (fun w hw => sub_ne_zero.mpr (fun h => by
        have hgt : a < w.re := hK (hsub hw)
        rw [h] at hgt
        exact (not_lt_of_ge (hre i)) hgt))
    change DifferentiableOn ℂ (fun w : ℂ => (mult i : ℂ) * ((w-xi i)⁻¹ - (z₀-xi i)⁻¹)) V
    exact (hinv.sub_const ((z₀-xi i)⁻¹)).const_mul (mult i : ℂ)
  have hb (i : ι) (w : ℂ) (hw : w ∈ V) : ‖F i w‖ ≤ M i := by
    have hw' : a < w.re := hK (hsub hw)
    have hl := fullCandidate_weighted_angular_limit w z₀ (xi i)
      ((hre i).trans_lt hw') ((hre i).trans_lt hz₀)
    have hnorm : ‖relative w z₀ (xi i)‖ ≤ D/(1+(xi i).im^2) :=
      le_of_tendsto hl.norm (Filter.Eventually.of_forall fun n =>
        hbound n w (hsub hw) (xi i).re (hstrip i) (xi i).im)
    rw [show F i w = (mult i : ℂ)*relative w z₀ (xi i) by rfl, norm_mul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)).trans_eq (by dsimp [M]; ring)
  exact ((Complex.differentiableOn_tsum_of_summable_norm hM hd Metric.isOpen_ball hb z
    (Metric.mem_ball_self (by positivity))).differentiableAt
      (Metric.ball_mem_nhds z (by positivity))).differentiableWithinAt

end RHConnections.SpectralTail
