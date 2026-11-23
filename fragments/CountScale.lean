import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace RHConnections.SpectralTail

theorem cumulative_count_dyadic (N : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ T : ℝ, 1 ≤ T → N T ≤ C * (T + 2) * Real.log (T + 2))
    (j : ℕ) :
    N ((2 : ℝ) ^ (j + 1)) ≤
      (8 * C * Real.log 2) * ((j : ℝ) + 1) * (2 : ℝ) ^ j := by
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hend : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hsize : (2 : ℝ) ^ (j + 1) + 2 ≤ 4 * 2 ^ j := by
    rw [pow_succ]
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log ((2 : ℝ) ^ (j + 1) + 2) ≤
      (2 * ((j : ℝ) + 1)) * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (j + 2)) := by
        apply Real.log_le_log (by positivity)
        calc
          _ ≤ 4 * (2 : ℝ) ^ j := hsize
          _ = (2 : ℝ) ^ (j + 2) := by rw [pow_add]; ring
      _ = ((j : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) j]) hlog2
  calc
    _ ≤ _ := hN _ hend
    _ ≤ (C * (4 * 2 ^ j)) * ((2 * ((j : ℝ) + 1)) * Real.log 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsize hC) hlog
        (Real.log_nonneg (by linarith)) (by positivity)
    _ = _ := by ring

#print axioms cumulative_count_dyadic
end RHConnections.SpectralTail
