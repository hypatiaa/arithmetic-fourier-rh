import Verified

open Filter Set MeasureTheory Asymptotics HurwitzZeta
noncomputable section
namespace RHConnections.SpectralTail
open ZetaMellinSplit

theorem thetaTail_measurable : Measurable thetaTail := by
  classical
  unfold thetaTail
  change Measurable ((Set.Ioi (1 : ℝ)).piecewise (fun x => ((evenKernel 0 x - 1 : ℝ) : ℂ)) (fun _ => 0))
  apply ContinuousOn.measurable_piecewise _ continuous_zero.continuousOn measurableSet_Ioi
  have h : ContinuousOn (evenKernel 0) (Set.Ioi (1 : ℝ)) :=
    (continuousOn_evenKernel 0).mono (fun x hx => Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp hx)))
  exact Complex.continuous_ofReal.comp_continuousOn (h.sub continuousOn_const)

theorem thetaTail_exponential : ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧
    ∀ x : ℝ, 1 < x → ‖thetaTail x‖ ≤ C * Real.exp (-p*x) := by
  obtain ⟨p, hp, h⟩ := isBigO_atTop_evenKernel_sub 0
  obtain ⟨C₀, h₀⟩ := isBigO_iff.mp h
  obtain ⟨R, hR⟩ := eventually_atTop.mp h₀
  let A : ℝ → ℝ := fun x => ‖evenKernel 0 x - 1‖ * Real.exp (p*x)
  have hA : ContinuousOn A (Set.Icc (1 : ℝ) (max R 1)) := by
    exact (((continuousOn_evenKernel 0).mono (fun x hx => zero_lt_one.trans_le hx.1)).sub
      continuousOn_const).norm.mul (by fun_prop)
  obtain ⟨C₁, h₁⟩ := isCompact_Icc.bddAbove_image hA
  let C := max (max C₀ C₁) 0
  refine ⟨p, C, hp, le_max_right _ _, ?_⟩
  intro x hx
  have hnorm : ‖thetaTail x‖ = ‖evenKernel 0 x - 1‖ := by
    simp only [thetaTail, indicator_of_mem (Set.mem_Ioi.mpr hx), Complex.norm_real]
  rw [hnorm]
  by_cases hRx : R ≤ x
  · have hh := hR x hRx
    simp only [if_pos rfl, Real.norm_of_nonneg (Real.exp_pos _).le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C₀ C₁).trans (le_max_left _ (0 : ℝ))) (Real.exp_pos _).le)
  · have hh := h₁ (mem_image_of_mem A
      (show x ∈ Set.Icc (1 : ℝ) (max R 1) from ⟨hx.le, (le_of_not_ge hRx).trans (le_max_left _ _)⟩))
    have hb : A x ≤ C := hh.trans ((le_max_right C₀ C₁).trans (le_max_left _ (0 : ℝ)))
    calc
      _ = A x * Real.exp (-p*x) := by
        dsimp [A]
        rw [mul_assoc, ← Real.exp_add, show p*x + -p*x = 0 by ring, Real.exp_zero, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

theorem completed_zeta_mellin_growth : ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ (s : ℂ) (R : ℝ),
    0 ≤ R → (s/2).re - 1 ≤ R → ((1-s)/2).re - 1 ≤ R →
    ‖completedRiemannZeta₀ s‖ ≤ (C * Real.exp (R*Real.log (1+2*R/p))) * (2/p) := by
  obtain ⟨p, C, hp, hC, h⟩ := thetaTail_exponential
  refine ⟨p, C, hp, hC, ?_⟩
  intro s R hR hs hs'
  have hz : ∀ x ≤ 1, thetaTail x = 0 := fun x hx => indicator_of_notMem
    (notMem_Ioi.mpr hx) _
  have h₁ := (mellin_exp_tail_bound thetaTail thetaTail_measurable hz hp hC hR h (s/2) hs).2
  have h₂ := (mellin_exp_tail_bound thetaTail thetaTail_measurable hz hp hC hR h ((1-s)/2) hs').2
  rw [completedRiemannZeta₀_mellin_split, norm_div, Complex.norm_two]
  exact (div_le_iff₀ (by norm_num)).2 ((norm_add_le _ _).trans (by linarith))

end RHConnections.SpectralTail
