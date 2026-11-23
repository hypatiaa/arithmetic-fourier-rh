import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

open Matrix
namespace RHConnections.FiniteCarrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allOnes : Matrix ι ι ℚ := fun _ _ => 1
def numerator (t : ℚ) : Matrix ι ι ℚ := t • 1 - allOnes

theorem allOnes_sq : (allOnes : Matrix ι ι ℚ) * allOnes =
    (Fintype.card ι : ℚ) • allOnes := by
  ext i j
  simp [allOnes, Matrix.mul_apply]

theorem numerator_sq (t : ℚ) :
    (numerator t : Matrix ι ι ℚ) * numerator t =
      t • numerator t + ((Fintype.card ι : ℚ) - t) • allOnes := by
  unfold numerator
  rw [sub_mul, mul_sub, mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    smul_smul, allOnes_sq]
  module

theorem additive_carrier (T : ℕ) :
    (numerator (T : ℚ) : Matrix (Fin T) (Fin T) ℚ) * numerator T =
      (T : ℚ) • numerator T := by
  simpa using (numerator_sq (ι := Fin T) (T : ℚ))

theorem unit_carrier (T : ℕ) (hT : 1 ≤ T) :
    (numerator (T : ℚ) : Matrix (Fin (T-1)) (Fin (T-1)) ℚ) * numerator T =
      (T : ℚ) • numerator T - allOnes := by
  have hc : (Fintype.card (Fin (T-1)) : ℚ) - (T : ℚ) = -1 := by
    simp only [Fintype.card_fin, Nat.cast_sub hT, Nat.cast_one]
    ring
  rw [numerator_sq, hc]
  simp [sub_eq_add_neg]

theorem numerator_on_zero_sum (t : ℚ) (v : ι → ℚ)
    (hv : ∑ i, v i = 0) : (numerator t).mulVec v = t • v := by
  unfold numerator
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hz : (allOnes : Matrix ι ι ℚ).mulVec v = 0 := by
    ext i
    simp [allOnes, Matrix.mulVec, dotProduct, hv]
  rw [hz, sub_zero]

theorem same_entries {T : ℕ} (x y : Fin (T-1)) :
    numerator (ι := Fin (T-1)) T x y = if x = y then (T : ℚ)-1 else -1 := by
  by_cases h : x = y <;> simp [numerator, allOnes, Matrix.one_apply, h]

#print axioms allOnes_sq
#print axioms numerator_sq
#print axioms additive_carrier
#print axioms unit_carrier
#print axioms numerator_on_zero_sum
end RHConnections.FiniteCarrier
