import Verified
import Mathlib.NumberTheory.LSeries.Dirichlet

noncomputable section
namespace RHConnections.DirichletGeometricLimit
open ArithmeticFunction Filter RelativeResolvent Mollifier FourierDecay
open scoped Topology

open scoped LSeries.notation
variable {N : ℕ} (χ : DirichletCharacter ℂ N)
private abbrev coeff : ℕ → ℂ := ↗χ * ↗vonMangoldt

def halfWeight (m : ℕ) : ℂ := LSeries.term (coeff χ) (1/2) m

theorem halfWeight_zero_of_nonunit (m : ℕ) (hm : ¬ IsUnit (m : ZMod N)) :
    halfWeight χ m = 0 := by
  have hχ : χ (m : ZMod N) = 0 := MulChar.map_nonunit χ hm
  by_cases h : m = 0
  · simp [halfWeight, h]
  · simp [halfWeight, LSeries.term_of_ne_zero h, coeff, hχ]

private theorem shiftTerm (m : ℕ) (z : ℂ) :
    halfWeight χ m * Complex.exp (-z * (Real.log m : ℂ)) =
      LSeries.term (coeff χ) (z+1/2) m := by
  by_cases hm : m = 0
  · subst m
    simp [halfWeight]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  simp only [halfWeight, LSeries.term_of_ne_zero hm, Complex.cpow_def_of_ne_zero hm',
    div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add,
    ← Complex.natCast_log]
  congr 2 <;> ring

private theorem relativeTerm (m : ℕ) (z z₀ : ℂ) :
    halfWeight χ m * logTest z z₀ (Real.log m) =
      LSeries.term (coeff χ) (z+1/2) m - LSeries.term (coeff χ) (z₀+1/2) m := by
  by_cases hm : 1 < m
  · rw [logTest, if_pos (Real.log_pos (by exact_mod_cast hm)), mul_sub, shiftTerm χ, shiftTerm χ]
  · have h : m = 0 ∨ m = 1 := by omega
    rcases h with rfl | rfl <;> simp [halfWeight, logTest, coeff]

theorem twisted_vonMangoldt_candidate_limit (z z₀ : ℂ)
    (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    (∀ k, Summable (fun m : ℕ => ‖halfWeight χ m * fullCandidate k z z₀ (Real.log m)‖)) ∧
    Tendsto (fun k => ∑' m : ℕ, halfWeight χ m * fullCandidate k z z₀ (Real.log m))
      atTop (𝓝 ((-deriv (LSeries ↗χ) (z+1/2) / LSeries ↗χ (z+1/2)) -
        (-deriv (LSeries ↗χ) (z₀+1/2) / LSeries ↗χ (z₀+1/2)))) := by
  let b := min z.re z₀.re
  have hb : 1/2 < b := lt_min hz hz₀
  have hshift (w : ℂ) (hw : 1/2 < w.re) : 1 < (w+1/2).re := by
    norm_num at * <;> linarith
  have hs (w : ℂ) (hw : 1/2 < w.re) : Summable (LSeries.term (coeff χ) (w+1/2)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (hshift w hw)
  let D := 2 * Real.exp (3 * |b|)
  let B := fun m => D * ‖LSeries.term (coeff χ) ((b : ℂ)+1/2) m‖
  have hB : Summable B := ((hs (b : ℂ) (by simpa using hb)).norm).mul_left D
  have hbound (k m : ℕ) :
      ‖halfWeight χ m * fullCandidate k z z₀ (Real.log m)‖ ≤ B m := by
    have h := fullCandidate_exponential_envelope k z z₀ b (Real.log m)
      (min_le_left _ _) (min_le_right _ _)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq ?_
    dsimp only [B, D]
    rw [← shiftTerm χ, norm_mul, Complex.norm_exp, Real.exp_sub, div_eq_mul_inv,
      ← Real.exp_neg]
    simp [← Complex.natCast_log] <;> ring
  have hlim := tendsto_tsum_of_dominated_convergence hB
    (fun m => tendsto_const_nhds.mul (fullCandidate_limit z z₀ (Real.log m)))
    (Eventually.of_forall hbound)
  refine ⟨fun k => hB.of_nonneg_of_le (fun _ => norm_nonneg _) (hbound k), ?_⟩
  have heq : (∑' m : ℕ, halfWeight χ m * logTest z z₀ (Real.log m)) =
      LSeries (coeff χ) (z+1/2) - LSeries (coeff χ) (z₀+1/2) := by
    simp_rw [relativeTerm χ]
    exact (hs z hz).tsum_sub (hs z₀ hz₀)
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ (hshift z hz),
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ (hshift z₀ hz₀)] at heq
  rwa [← heq]

end RHConnections.DirichletGeometricLimit
