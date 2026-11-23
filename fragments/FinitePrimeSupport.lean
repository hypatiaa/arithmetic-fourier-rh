import Verified

noncomputable section
namespace RHConnections.PoleCompensation
open EulerGeometricLimit Mollifier

theorem primeTest_eq_finite_sum (n : ℕ) (z z₀ : ℂ) :
    primeTest n z z₀ =
      ∑ k ∈ Finset.range (⌊Real.exp (2*((n : ℝ)+1))⌋₊ + 1),
        halfWeight k * fullCandidate n z z₀ (Real.log k) := by
  unfold primeTest
  apply tsum_eq_sum
  intro k hk
  have hnat : ⌊Real.exp (2*((n : ℝ)+1))⌋₊ < k := by
    exact Nat.lt_of_succ_le (Nat.le_of_not_gt fun h => hk (Finset.mem_range.mpr h))
  have hlt : Real.exp (2*((n : ℝ)+1)) < (k : ℝ) := (Nat.floor_lt (Real.exp_pos _).le).mp hnat
  have hp : 0 < (k : ℝ) := (Real.exp_pos _).trans hlt
  have hx : 2*((n : ℝ)+1) ≤ Real.log (k : ℝ) := by
    apply le_of_lt
    exact (Real.lt_log_iff_exp_lt hp).2 hlt
  have hb : cutoff n (Real.log k) = 0 := (cutoff n).zero_of_le_dist (by
    simp only [cutoff, Real.dist_eq, sub_zero]
    exact hx.trans (le_abs_self _))
  simp [fullCandidate, hb]

end RHConnections.PoleCompensation
