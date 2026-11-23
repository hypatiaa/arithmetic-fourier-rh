import Verified
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set
noncomputable section
namespace RHConnections.PerronRampBounds

private theorem positive_half (g : ℝ → ℝ) (hg : Integrable g)
    {H η D : ℝ} (hH : 0 < H) (hη : 0 < η) (hη₁ : η < 1)
    (h₁ : ∀ t, 0 < t → g t ≤ D*t^(η-1))
    (h₂ : ∀ t, 0 < t → g t ≤ (D*H)*t^(η-2)) :
    (∫ t in Ioi (0:ℝ), g t) ≤ D*(1/η + 1/(1-η))*H^η := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := H)
    (show -1 < η-1 by linarith)
  have hfar := integrableOn_Ioi_rpow_of_lt (show η-2 < -1 by linarith) hH
  have hshort : (∫ t in Ioc (0:ℝ) H, g t) ≤ D*(H^η/η) := by
    calc
      _ ≤ ∫ t in Ioc (0:ℝ) H, D*t^(η-1) := integral_mono_ae hg.integrableOn
        (hi.1.const_mul D) ((ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ fun t ht => h₁ t ht.1))
      _ = _ := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hH.le,
          integral_rpow (.inl (show -1 < η-1 by linarith)), show η-1+1=η by ring,
          Real.zero_rpow hη.ne', sub_zero]
  have hlong : (∫ t in Ioi H, g t) ≤ D*(H^η/(1-η)) := by
    calc
      _ ≤ ∫ t in Ioi H, (D*H)*t^(η-2) := integral_mono_ae hg.integrableOn
        (hfar.const_mul _) ((ae_restrict_iff' measurableSet_Ioi).mpr
          (ae_of_all _ fun t ht => h₂ t (hH.trans ht)))
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hH,
          show η-2+1=η-1 by ring, Real.rpow_sub hH, Real.rpow_one]
        rw [show η-1 = -(1-η) by ring]
        field_simp [hH.ne', (sub_pos.mpr hη₁).ne'] <;> ring
  have he : Ioi (0:ℝ) = Ioc 0 H ∪ Ioi H := by
    ext t
    change 0 < t ↔ (0 < t ∧ t ≤ H) ∨ H < t
    constructor
    · intro ht; by_cases h : t ≤ H
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (ht|ht)
      · exact ht.1
      · exact hH.trans ht
  have hd : Disjoint (Set.Ioc (0:ℝ) H) (Set.Ioi H) := Set.disjoint_left.mpr fun _ ha hb => (not_lt.mpr ha.2) hb
  rw [he, setIntegral_union (s := Set.Ioc (0:ℝ) H) (t := Set.Ioi H) hd
    measurableSet_Ioi hg.integrableOn hg.integrableOn]
  exact (add_le_add hshort hlong).trans_eq (by ring)

theorem weighted_kernel_integral_bound {b η : ℝ} (hb : 0 < b) (hb₃ : b ≤ 3)
    (hη : 0 < η) (hη₁ : η < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∫ t : ℝ, (1+|t|)^η * ‖kernel h (vertical b t)‖) ≤ A*h^(-η) := by
  let C := 1+b⁻¹
  let M := 2+Real.exp 3
  let D := C^η*M
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hgap : 0 < 1-η := by linarith
  refine ⟨2*(D*(1/η + 1/(1-η))), by positivity, ?_⟩
  intro h hh hh₁
  let G := fun t : ℝ => (1+|t|)^η * ‖kernel h (vertical b t)‖
  have hg : Integrable G := weighted_kernel_integrable hh hh₁ hb hb₃ hη₁
  have ht (t : ℝ) (ht : 0 < |t|) :
      G t ≤ D*|t|^(η-1) ∧ G t ≤ (D*h⁻¹)*|t|^(η-2) := by
    let s := vertical b t
    have hre : s.re = b := by simp [s,vertical]
    have him : s.im = t := by simp [s,vertical]
    have hbr : b ≤ ‖s‖ := by simpa only [hre] using Complex.re_le_norm s
    have htr : |t| ≤ ‖s‖ := by simpa only [him] using Complex.abs_im_le_norm s
    have hn : 0 < ‖s‖ := hb.trans_le hbr
    have hscale : 1+|t| ≤ C*‖s‖ := by
      have hi : 1 ≤ b⁻¹*‖s‖ := by
        calc
          _ = b⁻¹*b := (inv_mul_cancel₀ hb.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hbr (by positivity)
      dsimp [C]; nlinarith
    have hw := Real.rpow_le_rpow (show 0 ≤ 1+|t| by positivity) hscale hη.le
    rw [Real.mul_rpow hC.le hn.le] at hw
    obtain ⟨hk₁,hk₂⟩ := le_min_iff.mp (kernel_norm_min hh hh₁ hb hb₃ t)
    constructor
    · calc
        _ ≤ (C^η*‖s‖^η)*(M/‖s‖) := mul_le_mul hw hk₁ (norm_nonneg _) (by positivity)
        _ = D*‖s‖^(η-1) := by rw [Real.rpow_sub hn, Real.rpow_one]; dsimp [D]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht htr (by linarith)) hD
    · have hq : ‖kernel h s‖ ≤ M/(h*‖s‖^2) := hk₂.trans
        (div_le_div_of_nonneg_right (by dsimp [M]; linarith) (by positivity))
      calc
        _ ≤ (C^η*‖s‖^η)*(M/(h*‖s‖^2)) := mul_le_mul hw hq (norm_nonneg _) (by positivity)
        _ = (D*h⁻¹)*‖s‖^(η-2) := by rw [Real.rpow_sub hn]; dsimp [D]; norm_num; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht htr (by linarith))
          (mul_nonneg hD (inv_nonneg.mpr hh.le))
  have hfor (g : ℝ → ℝ) (hig : Integrable g)
      (hf : ∀ t, 0 < t → g t ≤ D*t^(η-1) ∧ g t ≤ (D*h⁻¹)*t^(η-2)) :=
    positive_half g hig (inv_pos.mpr hh) hη hη₁ (fun t h => (hf t h).1) (fun t h => (hf t h).2)
  have hpos := hfor G hg (fun t h => by simpa [abs_of_pos h] using ht t (abs_pos.mpr h.ne'))
  have hneg := hfor (fun t => G (-t)) hg.comp_neg (fun t h => by
    simpa [abs_neg, abs_of_pos h] using ht (-t) (by simpa [abs_of_pos h] using h))
  rw [integral_comp_neg_Ioi, neg_zero] at hneg
  have he := integral_add_compl measurableSet_Iic (f := G) (s := Iic (0:ℝ)) hg
  rw [compl_Iic] at he
  change (∫ t, G t) ≤ _
  rw [← he]
  have hp : (h⁻¹)^η = h^(-η) := by rw [Real.inv_rpow hh.le, Real.rpow_neg hh.le]
  exact (add_le_add hneg hpos).trans_eq (by rw [hp]; ring)

end RHConnections.PerronRampBounds
