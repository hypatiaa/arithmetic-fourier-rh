import Verified
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd

open Filter Set Asymptotics HurwitzZeta
noncomputable section
namespace RHConnections.HurwitzTailGrowth

theorem exp_bound_above_one {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : ContinuousOn f (Set.Ioi (0:ℝ)))
    (h : f =O[atTop] (fun x => Real.exp (-p*x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 < x → ‖f x‖ ≤ C * Real.exp (-p*x) := by
  obtain ⟨C₀,hC₀⟩ := isBigO_iff.mp h
  obtain ⟨R,hR⟩ := eventually_atTop.mp hC₀
  let g := fun x => ‖f x‖ * Real.exp (p*x)
  have hcont : ContinuousOn g (Set.Icc (1:ℝ) (max R 1)) :=
    (hf.mono (fun x hx => zero_lt_one.trans_le hx.1)).norm.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  obtain ⟨C₁,hC₁⟩ := isCompact_Icc.bddAbove_image hcont
  let C := max (max C₀ C₁) 0
  have h0 : C₀ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h1 : C₁ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  by_cases hr : R ≤ x
  · have hh := hR x hr
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le)
  · have hmem : x ∈ Set.Icc (1:ℝ) (max R 1) := ⟨hx.le,
      (le_of_not_ge hr).trans (le_max_left _ _)⟩
    calc
      _ = g x * Real.exp (-p*x) := by
        dsimp [g]
        rw [mul_assoc, ← Real.exp_add, show p*x + -p*x = 0 by ring,
          Real.exp_zero, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((hC₁ (Set.mem_image_of_mem _ hmem)).trans h1) (Real.exp_pos _).le

theorem hurwitzEven_tail_decay (a : UnitAddCircle) :
    (∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
      ‖(hurwitzEvenFEPair a).f_modif x‖ ≤ C * Real.exp (-p*x)) ∧
    (∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
      ‖(hurwitzEvenFEPair a).g_modif x‖ ≤ C * Real.exp (-p*x)) := by
  obtain ⟨p,hp,hp'⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨q,hq,hq'⟩ := isBigO_atTop_cosKernel_sub a
  classical
  obtain ⟨C,hC,hf⟩ := exp_bound_above_one hp
    ((continuousOn_evenKernel a).sub continuousOn_const) hp'
  obtain ⟨D,hD,hg⟩ := exp_bound_above_one hq
    ((continuousOn_cosKernel a).sub continuousOn_const) hq'
  constructor
  · refine ⟨p,C,hp,hC,fun x hx => ?_⟩
    have ho : x ∉ Set.Ioo (0:ℝ) 1 := Set.notMem_Ioo_of_ge hx.le
    have hc : (((evenKernel a x - (if a = 0 then 1 else 0) : ℝ) : ℂ)) =
        (evenKernel a x : ℂ) - (if a = 0 then 1 else 0) := by
      rw [Complex.ofReal_sub]
      split_ifs <;> norm_num
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_notMem ho, add_zero,
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx), hurwitzEvenFEPair, Function.comp_apply]
    rw [← hc, Complex.norm_real]
    exact hf x hx
  · refine ⟨q,D,hq,hD,fun x hx => ?_⟩
    have ho : x ∉ Set.Ioo (0:ℝ) 1 := Set.notMem_Ioo_of_ge hx.le
    have hc : (((cosKernel a x - 1 : ℝ) : ℂ)) = (cosKernel a x : ℂ) - 1 := by norm_num
    simp only [WeakFEPair.g_modif, Pi.add_apply, Set.indicator_of_notMem ho, add_zero,
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx), hurwitzEvenFEPair, Function.comp_apply]
    rw [← hc, Complex.norm_real]
    exact hg x hx

theorem hurwitzOdd_tail_decay (a : UnitAddCircle) :
    (∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
      ‖(hurwitzOddFEPair a).f_modif x‖ ≤ C * Real.exp (-p*x)) ∧
    (∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
      ‖(hurwitzOddFEPair a).g_modif x‖ ≤ C * Real.exp (-p*x)) := by
  obtain ⟨p,hp,hp'⟩ := isBigO_atTop_oddKernel a
  obtain ⟨q,hq,hq'⟩ := isBigO_atTop_sinKernel a
  obtain ⟨C,hC,hf⟩ := exp_bound_above_one hp (continuousOn_oddKernel a) hp'
  obtain ⟨D,hD,hg⟩ := exp_bound_above_one hq (continuousOn_sinKernel a) hq'
  constructor
  · refine ⟨p,C,hp,hC,fun x hx => ?_⟩
    have ho : x ∉ Set.Ioo (0:ℝ) 1 := Set.notMem_Ioo_of_ge hx.le
    simpa [WeakFEPair.f_modif, hurwitzOddFEPair, ho, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)] using hf x hx
  · refine ⟨q,D,hq,hD,fun x hx => ?_⟩
    have ho : x ∉ Set.Ioo (0:ℝ) 1 := Set.notMem_Ioo_of_ge hx.le
    simpa [WeakFEPair.g_modif, WeakFEPair.f_modif, WeakFEPair.symm, hurwitzOddFEPair, ho, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)] using hg x hx

end RHConnections.HurwitzTailGrowth
