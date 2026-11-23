import RelativeResolvent
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace RHConnections.RelativeResolvent

theorem logTest_continuous (z z₀ : ℂ) : Continuous (logTest z z₀) := by
  have hh : Continuous (fun x : ℝ =>
      if x ≤ 0 then (0 : ℂ) else Complex.exp (-z*(x : ℂ))-Complex.exp (-z₀*(x : ℂ))) := by
    apply Continuous.if_le continuous_const (by fun_prop) continuous_id continuous_const
    intro x hx
    change x = 0 at hx
    subst x
    simp
  convert hh using 1
  ext x
  simp only [logTest]
  by_cases h : 0 < x
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

theorem norm_difference_lower (z xi : ℂ) (h : 2*‖z‖ ≤ ‖xi‖) :
    ‖xi‖/2 ≤ ‖z-xi‖ := by
  have ht := norm_sub_norm_le xi z
  rw [norm_sub_rev xi z] at ht
  linarith

theorem relative_tail_bound (z z₀ xi : ℂ) (hxi : 0 < ‖xi‖)
    (hz : 2*‖z‖ ≤ ‖xi‖) (hz₀ : 2*‖z₀‖ ≤ ‖xi‖) :
    ‖relative z z₀ xi‖ ≤ 4*‖z₀-z‖ / ‖xi‖^2 := by
  have h1 := norm_difference_lower z xi hz
  have h2 := norm_difference_lower z₀ xi hz₀
  have hp1 : 0 < ‖z-xi‖ := by linarith
  have hp2 : 0 < ‖z₀-xi‖ := by linarith
  rw [reference_subtraction z z₀ xi (norm_pos_iff.mp hp1) (norm_pos_iff.mp hp2),
    norm_div, norm_mul]
  have hprod : (‖xi‖/2)*(‖xi‖/2) ≤ ‖z-xi‖*‖z₀-xi‖ :=
    mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  calc
    ‖z₀-z‖ / (‖z-xi‖*‖z₀-xi‖) ≤ ‖z₀-z‖ / ((‖xi‖/2)*(‖xi‖/2)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod
    _ = 4*‖z₀-z‖ / ‖xi‖^2 := by ring

#print axioms logTest_continuous
#print axioms norm_difference_lower
#print axioms relative_tail_bound
end RHConnections.RelativeResolvent
