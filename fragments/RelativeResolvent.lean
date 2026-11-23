import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace RHConnections.RelativeResolvent

def relative (z z₀ xi : ℂ) : ℂ := (z-xi)⁻¹ - (z₀-xi)⁻¹

theorem reference_subtraction (z z₀ xi : ℂ) (h : z-xi ≠ 0) (h₀ : z₀-xi ≠ 0) :
    relative z z₀ xi = (z₀-z) / ((z-xi)*(z₀-xi)) := by
  unfold relative
  field_simp
  <;> ring

theorem reference_vanishes (z xi : ℂ) : relative z z xi = 0 := by
  simp [relative]

theorem reference_cocycle (z w u xi : ℂ) :
    relative z w xi + relative w u xi = relative z u xi := by
  unfold relative
  ring

def logTest (z z₀ : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then Complex.exp (-z*(x : ℂ))-Complex.exp (-z₀*(x : ℂ)) else 0

theorem endpoint_zero (z z₀ : ℂ) : logTest z z₀ 0 = 0 := by
  simp [logTest]

theorem unsubtracted_endpoint_difference (z z₀ : ℂ) :
    Complex.exp (-z*(0 : ℂ))-Complex.exp (-z₀*(0 : ℂ)) = 0 := by simp

theorem vanishes_left (z z₀ : ℂ) {x : ℝ} (hx : x ≤ 0) :
    logTest z z₀ x = 0 := by simp [logTest, not_lt.mpr hx]

theorem diagonal_test (z : ℂ) (x : ℝ) : logTest z z x = 0 := by
  simp [logTest]

#print axioms reference_subtraction
#print axioms reference_cocycle
#print axioms endpoint_zero
end RHConnections.RelativeResolvent
