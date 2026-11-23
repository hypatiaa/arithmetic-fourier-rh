import Verified

open MeasureTheory
noncomputable section
namespace RHConnections.PerronRamp

private def poleCut (a : ℝ) : ℝ → ℝ := (Set.Ioc (0:ℝ) a).indicator Real.exp

private theorem poleCut_integrable (a : ℝ) :
    IntegrableOn (poleCut a) (Set.Ioi (0:ℝ)) := by
  apply Integrable.integrableOn
  exact (Real.continuous_exp.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).integrable_indicator
    measurableSet_Ioc

private theorem poleCut_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ u in Set.Ioi (0:ℝ), poleCut a u) = Real.exp a - 1 := by
  rw [poleCut, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le ha, integral_exp, Real.exp_zero]

theorem smoothedPole_error {h X : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hh₁ : h ≤ 1) :
    |smoothedPole h X - (X-1)| ≤ 3*X*h := by
  let x := Real.log X
  let L := max (x-h) 0
  let U := x+h
  let F := fun u : ℝ => Real.exp u * ramp h (x-u)
  have hp : 0 < X := by linarith
  have hx : 0 ≤ x := Real.log_nonneg hX
  have hL : 0 ≤ L := le_max_right _ _
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hcut (u : ℝ) (hu : 0 < u) : poleCut L u ≤ F u ∧ F u ≤ poleCut U u := by
    have hr := ramp_mem_Icc hh (x-u)
    constructor
    · by_cases hmem : u ≤ L
      · have hu' : u ≤ x-h := by
          rcases le_max_iff.mp hmem with hh'|hh'
          · exact hh'
          · linarith
        simp [poleCut, Set.indicator_of_mem (show u ∈ Set.Ioc 0 L from ⟨hu,hmem⟩),F,
          ramp_one hh (show _ ≤ x-u by linarith)]
      · rw [poleCut, Set.indicator_of_notMem (show u ∉ Set.Ioc 0 L from fun h' => hmem h'.2)]
        exact mul_nonneg (Real.exp_pos _).le hr.1
    · by_cases hmem : u ≤ U
      · rw [poleCut, Set.indicator_of_mem (show u ∈ Set.Ioc 0 U from ⟨hu,hmem⟩)]
        simpa [F] using mul_le_mul_of_nonneg_left hr.2 (Real.exp_pos u).le
      · rw [poleCut, Set.indicator_of_notMem (show u ∉ Set.Ioc 0 U from fun h' => hmem h'.2)]
        have hu' : x+h < u := lt_of_not_ge hmem
        simp [F,ramp_zero hh (show x-u ≤ -h by linarith)]
  have hFi : IntegrableOn F (Set.Ioi (0:ℝ)) := by
    apply (poleCut_integrable U).mono'
    · exact (Real.continuous_exp.mul ((ramp_continuous h).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      exact ae_of_all _ fun u hu => by
        have hn : 0 ≤ F u := mul_nonneg (Real.exp_pos _).le (ramp_mem_Icc hh _).1
        simpa only [Real.norm_of_nonneg hn] using (hcut u hu).2
  have hlo : Real.exp L - 1 ≤ smoothedPole h X := by
    rw [← poleCut_integral hL]
    exact integral_mono_ae (poleCut_integrable L) hFi
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => (hcut u hu).1))
  have hhi : smoothedPole h X ≤ Real.exp U - 1 := by
    rw [← poleCut_integral hU]
    exact integral_mono_ae hFi (poleCut_integrable U)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => (hcut u hu).2))
  have hlow := Real.exp_le_exp.mpr (le_max_left (x-h) 0)
  change Real.exp (x-h) ≤ Real.exp L at hlow
  rw [sub_eq_add_neg, Real.exp_add, show Real.exp x=X from Real.exp_log hp] at hlow
  have hhigh : Real.exp U = X*Real.exp h := by
    rw [show U=x+h from rfl,Real.exp_add,show Real.exp x=X from Real.exp_log hp]
  rw [hhigh] at hhi
  have h₁ : 1-Real.exp (-h) ≤ h := by linarith [Real.add_one_le_exp (-h)]
  have h₂ : Real.exp h-1 ≤ 2*h := by
    have h := Real.abs_exp_sub_one_le (show |h| ≤ 1 by simpa [abs_of_pos hh] using hh₁)
    exact (le_abs_self _).trans (by simpa [abs_of_pos hh] using h)
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h₁ hp.le,
    mul_le_mul_of_nonneg_left h₂ hp.le, mul_nonneg hp.le hh.le]

end RHConnections.PerronRamp
