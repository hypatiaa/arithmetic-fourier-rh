import Verified

open MeasureTheory Filter
noncomputable section
namespace RHConnections.ArchimedeanLimit
open Mollifier RelativeResolvent FourierDecay

def realPlaceKernel (x : ℝ) : ℝ := Real.exp (-x/2) / (1 - Real.exp (-2*x))

theorem realPlaceKernel_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ realPlaceKernel x := by
  have h : Real.exp (-2*x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr h.le)

theorem realPlaceKernel_denominator_bound {x : ℝ} (hx : 0 < x) :
    (2*x)/(1+2*x) ≤ 1 - Real.exp (-2*x) := by
  have h : Real.exp (-2*x) ≤ 1/(1+2*x) := by
    rw [show -2*x = -(2*x) by ring, Real.exp_neg, one_div]
    apply inv_anti₀ (by positivity)
    linarith only [Real.add_one_le_exp (2*x)]
  apply (div_le_iff₀ (by positivity)).2
  have hh := (le_div_iff₀ (by positivity : 0 < 1+2*x)).1 h
  nlinarith

theorem realPlaceKernel_limit {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    Tendsto (fun n => ∫ x in Set.Ioi (0 : ℝ),
      (realPlaceKernel x : ℂ) * fullCandidate n z z₀ x) atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), (realPlaceKernel x : ℂ) * logTest z z₀ x)) := by
  let c : ℝ := (3/2)*(‖z‖+‖z₀‖)
  let D : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator (fun _ => c) +
    (Set.Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-(1/2)*x))
  have hD : Integrable D := by
    apply Integrable.add
    · exact integrable_indicator_iff measurableSet_Ioc |>.2 (by simp)
    · exact integrable_indicator_iff measurableSet_Ioi |>.2
        ((integrableOn_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0) 1).const_mul 3)
  have hmeas : Measurable (fun x : ℝ => (realPlaceKernel x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (by unfold realPlaceKernel; fun_prop)
  apply tendsto_integral_of_dominated_convergence D
  · intro n
    exact hmeas.aestronglyMeasurable.mul (fullCandidate_smooth n z z₀).continuous.aestronglyMeasurable
  · exact hD.restrict
  · intro n
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hpos : 0 < x := hx
    have hd : 0 < 1 - Real.exp (-2*x) :=
      (div_pos (by positivity) (by positivity) : 0 < (2*x)/(1+2*x)).trans_le
        (realPlaceKernel_denominator_bound hpos)
    have hd' := (div_le_iff₀ (by positivity : 0 < 1+2*x)).mp
      (realPlaceKernel_denominator_bound hpos)
    rw [norm_mul, Complex.norm_of_nonneg (realPlaceKernel_nonneg hpos)]
    by_cases hx1 : x ≤ 1
    · have hK : realPlaceKernel x*x ≤ (3/2 : ℝ) := by
        unfold realPlaceKernel
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hd).2
        have hh := Real.exp_le_one_iff.mpr (show -x/2 ≤ 0 by linarith)
        have h1 := mul_le_mul_of_nonneg_right hh hpos.le
        have h2 := mul_le_mul_of_nonneg_left (show 1+2*x ≤ 3 by linarith) hd.le
        nlinarith
      have hDx : D x = c := by simp [D, show x ∈ Set.Ioc (0 : ℝ) 1 from ⟨hpos, hx1⟩, not_lt.mpr hx1]
      rw [hDx]
      calc
        _ ≤ realPlaceKernel x*((‖z‖+‖z₀‖)*x) :=
          mul_le_mul_of_nonneg_left (fullCandidate_linear n hz hz₀ hpos.le) (realPlaceKernel_nonneg hpos)
        _ = (realPlaceKernel x*x)*(‖z‖+‖z₀‖) := by ring
        _ ≤ c := mul_le_mul_of_nonneg_right hK (by positivity)
    · have hK : realPlaceKernel x ≤ (3/2)*Real.exp (-x/2) := by
        unfold realPlaceKernel
        apply (div_le_iff₀ hd).2
        have hp : 2/3 ≤ (2*x)/(1+2*x) := by
          apply (le_div_iff₀ (by positivity)).2
          linarith
        have hthree : 1 ≤ (3/2)*(1 - Real.exp (-2*x)) := by
          linarith [hp.trans (realPlaceKernel_denominator_bound hpos)]
        nlinarith [mul_le_mul_of_nonneg_right hthree (Real.exp_pos (-x/2)).le]
      have hDx : D x = 3 * Real.exp (-(1/2)*x) := by
        simp [D, show x ∉ Set.Ioc (0 : ℝ) 1 from fun h => hx1 h.2, lt_of_not_ge hx1]
      rw [hDx]
      have hf : ‖fullCandidate n z z₀ x‖ ≤ 2 := by
        simpa using fullCandidate_exponential_envelope n z z₀ 0 x hz hz₀
      exact (mul_le_mul hK hf (norm_nonneg _) (by positivity)).trans_eq (by
        rw [show -x/2 = -(1/2:ℝ)*x by ring]; ring)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (fullCandidate_limit z z₀ x)

end RHConnections.ArchimedeanLimit
