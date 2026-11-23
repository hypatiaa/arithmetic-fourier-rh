import Verified
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open Metric
noncomputable section
namespace RHConnections.SpectralTail

theorem entireXi_posLog_growth :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 3 ≤ R → ∀ s ∈ Metric.sphere (0 : ℂ) R,
      Real.posLog ‖entireXi s‖ ≤ K * R * Real.sqrt R := by
  obtain ⟨C, hC, hG⟩ := entireXi_jensen_growth
  refine ⟨12*C, by positivity, ?_⟩
  intro R hR s hs
  have hR0 : 0 ≤ R := by linarith
  have hnorm : ‖s‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
  let t := ‖s-(2:ℂ)‖
  have ht₁ : 1 ≤ t := by
    have hb := norm_sub_norm_le s (2:ℂ)
    rw [hnorm, Complex.norm_two] at hb
    dsimp only [t]
    linarith
  have ht₂ : t+2 ≤ 3*R := by
    have hb := norm_sub_le s (2:ℂ)
    rw [hnorm, Complex.norm_two] at hb
    dsimp only [t]
    linarith
  have hG' := hG t ht₁ s (show s ∈ Metric.sphere (2:ℂ) t by
    rw [Metric.mem_sphere, dist_eq_norm])
  have hu : 0 < t+2 := by linarith
  have hsqrt : Real.sqrt (t+2) ≤ 2*Real.sqrt R := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hR0]
  have hl : Real.log (t+2) ≤ 4*Real.sqrt R := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
    rw [Real.log_sqrt hu.le] at h
    linarith
  change max 0 (Real.log ‖entireXi s‖) ≤ _
  apply max_le (by positivity)
  calc
    _ ≤ C*(t+2)*Real.log (t+2) := hG'
    _ ≤ (C*(3*R))*(4*Real.sqrt R) := mul_le_mul
      (mul_le_mul_of_nonneg_left ht₂ hC) hl
      (Real.log_nonneg (by linarith)) (by positivity)
    _ = _ := by ring

#print axioms entireXi_posLog_growth
end RHConnections.SpectralTail
