import Verified
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

noncomputable section
namespace RHConnections.WeakFEPairMellinSplit
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def upperF (P : WeakFEPair E) := (Ioi (1 : ℝ)).indicator P.f_modif
def upperG (P : WeakFEPair E) := (Ioi (1 : ℝ)).indicator P.g_modif

private theorem cut_convergent {f : ℝ → E} {s : ℂ} {S : Set ℝ}
    (hm : MeasurableSet S) (hf : MellinConvergent f s) :
    MellinConvergent (S.indicator f) s := by
  unfold MellinConvergent at *
  apply (hf.indicator hm).congr
  filter_upwards with x
  by_cases hx : x ∈ S <;> simp [hx]

theorem upperF_convergent (P : WeakFEPair E) (s : ℂ) : MellinConvergent (upperF P) s :=
  cut_convergent measurableSet_Ioi (P.isStrongFEPair_toStrongFEPair.hasMellin s).1

theorem upperG_convergent (P : WeakFEPair E) (s : ℂ) : MellinConvergent (upperG P) s :=
  upperF_convergent P.symm s

theorem weakFEPair_mellin_split (P : WeakFEPair E) (s : ℂ) :
    P.Λ₀ s = mellin (upperF P) s + P.ε • mellin (upperG P) ((P.k:ℂ)-s) := by
  let lower := (Ioi (1:ℝ))ᶜ.indicator P.f_modif
  let w := fun u : ℝ => (u:ℂ)^(P.k:ℂ) • upperG P u
  have hsum : P.f_modif = fun u => upperF P u + lower u := by
    funext u
    by_cases h : u ∈ Ioi (1:ℝ)
    · have hc : u ∉ (Ioi (1:ℝ))ᶜ := fun h' => h' h
      simp only [upperF,lower,indicator_of_mem h,indicator_of_notMem hc,add_zero]
    · have hc : u ∈ (Ioi (1:ℝ))ᶜ := h
      simp only [upperF,lower,indicator_of_notMem h,indicator_of_mem hc,zero_add]
  have hl : MellinConvergent lower s :=
    cut_convergent measurableSet_Ioi.compl (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have he : mellin lower s = mellin (fun x : ℝ => (fun u => P.ε • w u) x⁻¹) s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with x hx hx1
    change (x:ℂ)^(s-1) • lower x = (x:ℂ)^(s-1) • (P.ε • w x⁻¹)
    congr 1
    have hx0 : 0 < x := hx
    rcases lt_or_gt_of_ne hx1 with hlt|hgt
    · have hi : 1 < x⁻¹ := by rw [← one_div, lt_div_iff₀ hx0, one_mul]; exact hlt
      have hc : x ∈ (Ioi (1:ℝ))ᶜ := not_lt.mpr hlt.le
      have hu : x⁻¹ ∈ Ioi (1:ℝ) := hi
      have h := P.hf_modif_FE x⁻¹ (inv_pos.mpr hx0)
      rw [one_div, inv_inv, Complex.ofReal_cpow (inv_pos.mpr hx0).le, mul_smul] at h
      simpa only [lower, upperG, w, indicator_of_mem hc, indicator_of_mem hu] using h
    · have hi : ¬1 < x⁻¹ := by
        rw [← one_div, not_lt, div_le_iff₀ hx0]
        simpa using hgt.le
      have hc : x ∉ (Ioi (1:ℝ))ᶜ := fun h => h hgt
      have hu : x⁻¹ ∉ Ioi (1:ℝ) := hi
      simp only [lower, w, upperG, indicator_of_notMem hc, indicator_of_notMem hu, smul_zero]
  change mellin P.f_modif s = _
  rw [hsum, (hasMellin_add (upperF_convergent P s) hl).2, he, mellin_comp_inv (fun u => P.ε • w u) s,
    mellin_const_smul, show mellin w (-s) = mellin (upperG P) (-s+(P.k:ℂ)) from
      mellin_cpow_smul _ _ _, show -s+(P.k:ℂ) = (P.k:ℂ)-s by ring]

end RHConnections.WeakFEPairMellinSplit
