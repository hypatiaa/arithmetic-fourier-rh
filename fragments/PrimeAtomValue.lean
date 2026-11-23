import Verified

noncomputable section
namespace RHConnections.EulerGeometricLimit

theorem prime_sum_eq_halfWeight_two (f : ℝ → ℂ) (h₂ : f (Real.log 2) = 1)
    (hoff : ∀ x : ℝ, x ∉ Set.Ioo 0 (Real.log 3) → f x = 0) :
    (∑' m : ℕ, halfWeight m * f (Real.log m)) = halfWeight 2 := by
  rw [tsum_eq_single 2]
  · simpa only [Nat.cast_ofNat, h₂, mul_one]
  · intro m hm
    by_cases h₀ : m = 0
    · subst m
      simp [halfWeight]
    by_cases h₁ : m = 1
    · subst m
      rw [Nat.cast_one, Real.log_one, hoff 0 (fun h => (lt_irrefl _) h.1), mul_zero]
    have h₃ : 3 ≤ m := by omega
    have hlog : Real.log 3 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h₃)
    rw [hoff _ (fun h => (not_lt_of_ge hlog) h.2), mul_zero]

theorem halfWeight_two_ne_zero : halfWeight 2 ≠ 0 := by
  rw [halfWeight, LSeries.term_of_ne_zero (by decide : (2:ℕ) ≠ 0)]
  change (ArithmeticFunction.vonMangoldt 2 : ℂ) / (2 : ℂ) ^ (1/2 : ℂ) ≠ 0
  apply div_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact (Real.log_pos (by norm_num)).ne'
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

#print axioms prime_sum_eq_halfWeight_two
#print axioms halfWeight_two_ne_zero
end RHConnections.EulerGeometricLimit
