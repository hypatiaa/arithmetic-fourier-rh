import Verified
import Mathlib.NumberTheory.LSeries.RiemannZeta

open MeasureTheory Set HurwitzZeta
noncomputable section
namespace RHConnections.ZetaMellinSplit

def thetaTail : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (fun x => ((evenKernel 0 x - 1 : ℝ) : ℂ))

private theorem tail_eq_upper :
    thetaTail = (Set.Ioi (1 : ℝ)).indicator (hurwitzEvenFEPair 0).f_modif := by
  funext x
  by_cases hx : 1 < x
  · have ho : x ∉ Set.Ioo (0 : ℝ) 1 := notMem_Ioo_of_ge hx.le
    simp [thetaTail, WeakFEPair.f_modif, Set.mem_Ioi.mpr hx, ho, hurwitzEvenFEPair]
  · simp [thetaTail, hx]

private theorem mellinConvergent_indicator {f : ℝ → ℂ} {u : ℂ} {S : Set ℝ}
    (hS : MeasurableSet S) (hf : MellinConvergent f u) :
    MellinConvergent (S.indicator f) u := by
  unfold MellinConvergent at *
  have h := hf.indicator hS
  apply h.congr
  filter_upwards with x
  by_cases hx : x ∈ S <;> simp [hx]

theorem thetaTail_convergent (u : ℂ) : MellinConvergent thetaTail u := by
  rw [tail_eq_upper]
  exact mellinConvergent_indicator measurableSet_Ioi
    (((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin u).1)

theorem completedRiemannZeta₀_mellin_split (s : ℂ) :
    completedRiemannZeta₀ s =
      (mellin thetaTail (s/2) + mellin thetaTail ((1-s)/2))/2 := by
  let P := hurwitzEvenFEPair 0
  let lower := (Set.Ioi (1 : ℝ))ᶜ.indicator P.f_modif
  have hsum : P.f_modif = fun x => thetaTail x + lower x := by
    rw [tail_eq_upper]
    funext x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · have hc : x ∉ (Set.Ioi (1 : ℝ))ᶜ := fun h => h hx
      simp only [lower, Set.indicator_of_mem hx, Set.indicator_of_notMem hc, add_zero, P]
    · have hc : x ∈ (Set.Ioi (1 : ℝ))ᶜ := hx
      simp only [lower, Set.indicator_of_notMem hx, Set.indicator_of_mem hc, zero_add, P]
  have hl : MellinConvergent lower (s/2) :=
    mellinConvergent_indicator measurableSet_Ioi.compl (P.isStrongFEPair_toStrongFEPair.hasMellin _).1
  let weighted (u : ℝ) := (u : ℂ) ^ (1/2 : ℂ) • thetaTail u
  have hlo : mellin lower (s/2) = mellin (fun x : ℝ => weighted x⁻¹) (s/2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (x : ℂ) ^ (s/2-1) • lower x = (x : ℂ) ^ (s/2-1) • weighted x⁻¹
    congr 1
    have hx0 : 0 < x := hx
    rcases lt_trichotomy x 1 with hlt | heq | hgt
    · have hinv : 1 < x⁻¹ := by
        rw [← one_div, lt_div_iff₀ hx0, one_mul]
        exact hlt
      have hfe := P.hf_modif_FE x⁻¹ (inv_pos.mpr hx0)
      have hmod : P.g_modif = P.f_modif := by
        change (hurwitzEvenFEPair 0).symm.f_modif = (hurwitzEvenFEPair 0).f_modif
        rw [hurwitzEvenFEPair_zero_symm]
      rw [hmod, one_div, inv_inv] at hfe
      have heps : P.ε = 1 := rfl
      have hk : P.k = 1/2 := rfl
      rw [heps, hk, one_mul, Complex.ofReal_cpow (inv_pos.mpr hx0).le] at hfe
      have hc : x ∈ (Set.Ioi (1 : ℝ))ᶜ := not_lt.mpr hlt.le
      have hu : x⁻¹ ∈ Set.Ioi (1 : ℝ) := hinv
      simp only [lower, weighted, tail_eq_upper, Set.indicator_of_mem hc, Set.indicator_of_mem hu]
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hfe
    · subst x
      simp [lower, weighted, thetaTail, WeakFEPair.f_modif]
    · have hi : ¬ 1 < x⁻¹ := by
        rw [← one_div, not_lt, div_le_iff₀ hx0]
        simpa using hgt.le
      have hc : x ∉ (Set.Ioi (1 : ℝ))ᶜ := fun h => h hgt
      have hu : x⁻¹ ∉ Set.Ioi (1 : ℝ) := hi
      simp only [lower, weighted, thetaTail, Set.indicator_of_notMem hc,
        Set.indicator_of_notMem hu, smul_zero]
  change mellin P.f_modif (s/2) / 2 = _
  rw [hsum, (hasMellin_add (thetaTail_convergent _) hl).2, hlo,
    mellin_comp_inv, show mellin weighted (-(s/2)) = mellin thetaTail (-(s/2)+(1/2 : ℂ)) from
      mellin_cpow_smul _ _ _, show -(s/2)+(1/2 : ℂ) = (1-s)/2 by ring]

#print axioms thetaTail_convergent
#print axioms completedRiemannZeta₀_mellin_split
end RHConnections.ZetaMellinSplit
