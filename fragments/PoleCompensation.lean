import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MeasureTheory
noncomputable section
namespace RHConnections.PoleCompensation

theorem trace_rearrangement {Gfin Ginf Pplus Pminus Z : ℂ}
    (trace : Gfin + Ginf = Pplus + Pminus - Z) :
    Gfin - Pplus = Pminus - Z - Ginf := by
  linear_combination trace

theorem relative_compensation (D D₀ P P₀ : ℂ) :
    (D-P)-(D₀-P₀) = (D-D₀)-(P-P₀) := by ring

def upperPoleMass (R : ℝ) : ℝ :=
  ∫ x in 0..R, Real.exp ((1/4:ℝ)*x)-Real.exp ((-1:ℝ)*x)

theorem upperPoleMass_formula (R : ℝ) :
    upperPoleMass R = 4*Real.exp ((1/4:ℝ)*R)+Real.exp ((-1:ℝ)*R)-5 := by
  have h1 : Continuous (fun x : ℝ => Real.exp ((1/4:ℝ)*x)) := by fun_prop
  have h2 : Continuous (fun x : ℝ => Real.exp ((-1:ℝ)*x)) := by fun_prop
  unfold upperPoleMass
  rw [intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (1/4:ℝ) ≠ 0),
    intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (-1:ℝ) ≠ 0)]
  simp only [smul_eq_mul, integral_exp, mul_zero, Real.exp_zero]
  norm_num
  ring

theorem upperPoleMass_unbounded :
    ∀ B : ℝ, ∃ R : ℝ, 0 < R ∧ B < upperPoleMass R := by
  intro B
  let c : ℝ := max B 0 + 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : 1 < c := by dsimp [c]; linarith [le_max_right B (0:ℝ)]
  refine ⟨4*Real.log c, mul_pos (by norm_num) (Real.log_pos hc1), ?_⟩
  rw [upperPoleMass_formula]
  have he : Real.exp ((1/4:ℝ)*(4*Real.log c)) = c := by
    convert Real.exp_log hc using 1 <;> ring
  rw [he]
  have hp := Real.exp_pos ((-1:ℝ)*(4*Real.log c))
  dsimp [c] at *
  linarith [le_max_left B (0:ℝ), le_max_right B (0:ℝ)]

#print axioms trace_rearrangement
#print axioms relative_compensation
#print axioms upperPoleMass_formula
#print axioms upperPoleMass_unbounded
end RHConnections.PoleCompensation
