import Verified

namespace RHConnections.BlockFourier

variable {ι : Type*} [Fintype ι]

theorem weighted_variance_split (v h : ι → ℝ) (c : ℝ)
    (hA : 0 < ∑ i, v i) :
    let A := ∑ i, v i
    let m := (∑ i, v i * h i) / A
    (∑ i, v i * (c + h i)^2) = A*(c+m)^2 + ∑ i, v i*(h i-m)^2 := by
  dsimp only
  let A := ∑ i, v i
  let m := (∑ i, v i * h i) / A
  change (∑ i, v i*(c+h i)^2) = A*(c+m)^2 + ∑ i, v i*(h i-m)^2
  have hzero : (∑ i, v i*(h i-m)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    change (∑ i, v i*h i) - A*m = 0
    dsimp [m]
    have ha : A ≠ 0 := hA.ne'
    rw [div_eq_mul_inv, ←mul_assoc, mul_comm A, mul_assoc, mul_inv_cancel₀ ha, mul_one, sub_self]
  calc
    (∑ i, v i*(c+h i)^2) =
        ∑ i, (v i*(c+m)^2 + 2*(c+m)*(v i*(h i-m)) + v i*(h i-m)^2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hzero, mul_zero, add_zero]
      rfl

theorem weighted_variance_minimum (v h : ι → ℝ) (c : ℝ)
    (hA : 0 < ∑ i, v i) :
    let m := (∑ i, v i*h i) / (∑ i, v i)
    (∑ i, v i*(-m+h i)^2) ≤ ∑ i, v i*(c+h i)^2 := by
  dsimp only
  let m := (∑ i, v i*h i) / (∑ i, v i)
  have hc := weighted_variance_split v h c hA
  have hm := weighted_variance_split v h (-m) hA
  change (∑ i, v i*(c+h i)^2) = (∑ i,v i)*(c+m)^2+∑ i,v i*(h i-m)^2 at hc
  change (∑ i, v i*(-m+h i)^2) = (∑ i,v i)*(-m+m)^2+∑ i,v i*(h i-m)^2 at hm
  change (∑ i,v i*(-m+h i)^2) ≤ ∑ i,v i*(c+h i)^2
  rw [hm, hc]
  simp only [neg_add_cancel, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
  exact le_add_of_nonneg_left (mul_nonneg hA.le (sq_nonneg _))

end RHConnections.BlockFourier
