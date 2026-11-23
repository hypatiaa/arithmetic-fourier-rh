import Mollifier

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
noncomputable section
namespace RHConnections.Mollifier
open RelativeResolvent

def cutoff (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (n : ℝ)+1
  rOut := 2*((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith

def fullCandidate (n : ℕ) (z z₀ : ℂ) (x : ℝ) : ℂ :=
  cutoff n x • smoothDelayed n z z₀ x

theorem fullCandidate_smooth (n : ℕ) (z z₀ : ℂ) :
    ContDiff ℝ ∞ (fullCandidate n z z₀) :=
  (cutoff n).contDiff.smul (smoothDelayed_smooth n z z₀)

theorem fullCandidate_compact (n : ℕ) (z z₀ : ℂ) :
    HasCompactSupport (fullCandidate n z z₀) :=
  (cutoff n).hasCompactSupport.smul_right

theorem cutoff_limit (x : ℝ) :
    Tendsto (fun n => cutoff n x) atTop (nhds 1) := by
  have he : ∀ᶠ n : ℕ in atTop, |x| ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop |x|)
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  symm
  apply (cutoff n).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |x| ≤ (n : ℝ)+1
  linarith

theorem fullCandidate_limit (z z₀ : ℂ) (x : ℝ) :
    Tendsto (fun n => fullCandidate n z z₀ x) atTop (nhds (logTest z z₀ x)) := by
  simpa only [fullCandidate, one_smul] using
    (cutoff_limit x).smul (smoothDelayed_limit z z₀ x)

theorem smoothDelayed_vanishes_left (n : ℕ) (z z₀ : ℂ) {x : ℝ}
    (hx : x ≤ epsilon n) : smoothDelayed n z z₀ x = 0 := by
  unfold smoothDelayed
  rw [MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : epsilon n ≤ |y|
  · have hb : bump n y = 0 := (bump n).zero_of_le_dist (by
      simpa only [bump, Real.dist_eq, sub_zero] using hy)
    simp [ContDiffBump.normed_def, hb]
  · have ht : x-2*epsilon n-y ≤ 0 := by
      have ha := neg_le_abs y
      have hlt : |y| < epsilon n := lt_of_not_ge hy
      linarith
    rw [vanishes_left z z₀ ht]
    simp

theorem fullCandidate_vanishes_left (n : ℕ) (z z₀ : ℂ) {x : ℝ}
    (hx : x ≤ epsilon n) : fullCandidate n z z₀ x = 0 := by
  simp [fullCandidate, smoothDelayed_vanishes_left n z z₀ hx]

#print axioms fullCandidate_smooth
#print axioms fullCandidate_compact
#print axioms cutoff_limit
#print axioms fullCandidate_limit
#print axioms smoothDelayed_vanishes_left
#print axioms fullCandidate_vanishes_left
end RHConnections.Mollifier
