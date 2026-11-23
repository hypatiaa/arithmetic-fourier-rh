import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open Set MeasureTheory

noncomputable section
namespace RHConnections.ArchimedeanCutoff

def density (u : ℝ) : ℝ := ((1 + u) ^ 2 * u)⁻¹

def truncatedMass (δ : ℝ) : ℝ := ∫ u in δ..1, density u

theorem pointwise_lower_bound {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (1 / 4 : ℝ) * u⁻¹ ≤ density u := by
  have hsq : (1 + u) ^ 2 ≤ (4 : ℝ) := by nlinarith
  have hpos : 0 < (1 + u) ^ 2 * u := by positivity
  have hle : (1 + u) ^ 2 * u ≤ 4 * u := mul_le_mul_of_nonneg_right hsq hu.le
  have hi := one_div_le_one_div_of_le hpos hle
  simpa [density, one_div, _root_.mul_inv_rev, mul_comm] using hi

theorem density_continuousOn {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn density (Icc δ 1) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro u hu
    have : 0 < u := lt_of_lt_of_le hδ hu.1
    positivity

theorem truncatedMass_lower_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 / 4 : ℝ) * Real.log (1 / δ) ≤ truncatedMass δ := by
  have hcont : ContinuousOn (fun u : ℝ => (1 / 4 : ℝ) * u⁻¹) (Icc δ 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le hδ hu.1)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hδ1
    (hcont.intervalIntegrable_of_Icc hδ1)
    ((density_continuousOn hδ).intervalIntegrable_of_Icc hδ1)
    (fun u hu => pointwise_lower_bound (lt_of_lt_of_le hδ hu.1) hu.2)
  rw [intervalIntegral.integral_const_mul,
    integral_inv_of_pos hδ (by norm_num)] at hmono
  exact hmono

theorem truncatedMass_unbounded :
    ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ B < truncatedMass δ := by
  intro B
  let c : ℝ := max B 0 + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let δ : ℝ := Real.exp (-(4 * c))
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ < 1 := by
    dsimp [δ]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hlog : Real.log (1 / δ) = 4 * c := by
    rw [one_div, Real.log_inv]
    dsimp [δ]
    rw [Real.log_exp]
    ring
  have hbound := truncatedMass_lower_bound hδ hδ1.le
  rw [hlog] at hbound
  refine ⟨δ, hδ, hδ1, ?_⟩
  have hBc : B < c := by dsimp [c]; linarith [le_max_left B (0 : ℝ)]
  linarith

#print axioms pointwise_lower_bound
#print axioms density_continuousOn
#print axioms truncatedMass_lower_bound
#print axioms truncatedMass_unbounded

end RHConnections.ArchimedeanCutoff
