import Verified
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
namespace RHConnections.CanonicalFactor

def genusOne (w : ℂ) : ℂ := (1-w) * Complex.exp w

theorem genusOne_differentiable : Differentiable ℂ genusOne := by
  unfold genusOne
  fun_prop

theorem norm_genusOne_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖genusOne w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have h : genusOne w - 1 = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by
    unfold genusOne
    ring
  rw [h]
  calc
    _ ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ = ‖Complex.exp w - 1 - w‖ + ‖w‖ * ‖Complex.exp w - 1‖ := by rw [norm_mul]
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := add_le_add
      (Complex.norm_exp_sub_one_sub_id_le hw)
      (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le hw) (norm_nonneg _))
    _ = 3 * ‖w‖ ^ 2 := by ring

theorem norm_genusOne_sub_one_le_on_disk {R : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) :
    ‖genusOne w - 1‖ ≤ max 3 ((1+R)*Real.exp R+1) * ‖w‖ ^ 2 := by
  by_cases hsmall : ‖w‖ ≤ 1
  · exact (norm_genusOne_sub_one_le hsmall).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have hr : 0 ≤ R := (norm_nonneg _).trans hw
  have he : ‖Complex.exp w‖ ≤ Real.exp R := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hw)
  have ha : ‖(1 : ℂ) - w‖ ≤ 1+R := by
    calc
      _ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 1+R := by simp only [norm_one]; exact add_le_add_right hw 1
  have h1 : 1 ≤ ‖w‖ ^ 2 := by nlinarith [lt_of_not_ge hsmall, sq_nonneg (‖w‖-1)]
  calc
    _ ≤ ‖genusOne w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (1+R)*Real.exp R+1 := by
      rw [genusOne, norm_mul, norm_one]
      exact add_le_add_left (mul_le_mul ha he (norm_nonneg _) (by linarith)) _
    _ ≤ max 3 ((1+R)*Real.exp R+1) := le_max_right _ _
    _ ≤ max 3 ((1+R)*Real.exp R+1) * ‖w‖ ^ 2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h1
        (show 0 ≤ max 3 ((1+R)*Real.exp R+1) from
          (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_left _ _))

#print axioms norm_genusOne_sub_one_le_on_disk
#print axioms genusOne_differentiable
#print axioms norm_genusOne_sub_one_le
end RHConnections.CanonicalFactor
