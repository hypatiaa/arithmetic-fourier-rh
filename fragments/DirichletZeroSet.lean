import Verified
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Filter
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter SpectralTail

variable {N : ℕ} [NeZero N]

abbrev DirichletNontrivialZero (χ : DirichletCharacter ℂ N) :=
  {s : ℂ // (0 < s.re ∧ s.re < 1) ∧ LFunction χ s = 0}

theorem gammaFactor_analytic_nonzero_pos (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (gammaFactor χ) s ∧ gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [show gammaFactor χ = Complex.Gammaℝ from funext he.gammaFactor_def]
    exact ⟨gamma_real_analytic_of_re_pos hs, gamma_real_nonzero_of_re_pos hs⟩
  · rw [show gammaFactor χ = fun t => Complex.Gammaℝ (t+1) from funext ho.gammaFactor_def]
    have hp : 0 < (s+1).re := by simp; linarith
    exact ⟨(gamma_real_analytic_of_re_pos hp).comp
      (f := fun t : ℂ => t+1) (analyticAt_id.add analyticAt_const),
      gamma_real_nonzero_of_re_pos hp⟩

theorem completed_dirichlet_germ (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ =ᶠ[nhds s] (fun t => gammaFactor χ t * LFunction χ t) := by
  have hU : {t : ℂ | 0 < t.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hU] with t ht
  have h0 : t ≠ 0 := by intro h; change 0 < t.re at ht; simpa [h] using ht
  exact ((eq_div_iff (gammaFactor_analytic_nonzero_pos χ ht).2).mp
    (LFunction_eq_completed_div_gammaFactor χ t (Or.inl h0))).symm.trans (mul_comm _ _)

theorem completed_dirichlet_nonzero_of_one_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    completedLFunction χ s ≠ 0 := by
  have hp : 0 < s.re := zero_lt_one.trans_le hs
  rw [(completed_dirichlet_germ χ hp).eq_of_nhds]
  exact mul_ne_zero (gammaFactor_analytic_nonzero_pos χ hp).2
    (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)

theorem primitive_rootNumber_nonzero {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) : rootNumber χ ≠ 0 := by
  intro hz
  have h := hp.completedLFunction_one_sub (-1)
  have h2 : (1:ℂ)-(-1) = 2 := by norm_num
  rw [h2,hz,mul_zero,zero_mul] at h
  exact completed_dirichlet_nonzero_of_one_le χ hχ (by norm_num) h

theorem completed_dirichlet_zero_iff {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    completedLFunction χ s = 0 ↔ (0 < s.re ∧ s.re < 1) ∧ LFunction χ s = 0 := by
  by_cases hr : 0 < s.re
  · by_cases h1 : s.re < 1
    · rw [(completed_dirichlet_germ χ hr).eq_of_nhds, mul_eq_zero]
      simp [hr,h1,(gammaFactor_analytic_nonzero_pos χ hr).2]
    · simp [h1,completed_dirichlet_nonzero_of_one_le χ hχ (le_of_not_gt h1)]
  · have hs' : 1 ≤ (1-s).re := by simp [Complex.sub_re]; linarith
    have hInv : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
    have hN : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    have hpow : (N:ℂ)^((1-s)-1/2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hN]; exact Complex.exp_ne_zero _
    have he := hp.completedLFunction_one_sub (1-s)
    rw [show 1-(1-s)=s by ring] at he
    have hn : completedLFunction χ s ≠ 0 := by
      rw [he]
      exact mul_ne_zero (mul_ne_zero hpow (primitive_rootNumber_nonzero hp hχ))
        (completed_dirichlet_nonzero_of_one_le χ⁻¹ hInv hs')
    simp [hr,hn]

theorem completed_dirichlet_order {χ : DirichletCharacter ℂ N}
    {s : ℂ} (hs : 0 < s.re) (hχ : χ ≠ 1) :
    analyticOrderAt (completedLFunction χ) s = analyticOrderAt (LFunction χ) s := by
  have hL : AnalyticAt ℂ (LFunction χ) s :=
    (differentiable_LFunction hχ).analyticAt s
  obtain ⟨hG,hG0⟩ := gammaFactor_analytic_nonzero_pos χ hs
  have hg : analyticOrderAt (gammaFactor χ) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hG0)
  rw [analyticOrderAt_congr (completed_dirichlet_germ χ hs)]
  change analyticOrderAt (gammaFactor χ * LFunction χ) s = _
  rw [analyticOrderAt_mul hG hL, hg, zero_add]

end RHConnections.DirichletZeroSet
