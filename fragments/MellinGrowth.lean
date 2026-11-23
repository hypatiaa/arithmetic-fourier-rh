import Verified
import Mathlib.Analysis.MellinTransform

open MeasureTheory
namespace RHConnections.SpectralTail

theorem power_exp_majorant {p R x : ℝ} (hp : 0 < p) (hR : 0 ≤ R) (hx : 0 < x) :
    x ^ R * Real.exp (-p*x) ≤
      Real.exp (R*Real.log (1+2*R/p)) * Real.exp (-(p/2)*x) := by
  let B : ℝ := 1+2*R/p
  have hB : 0 < B := by dsimp [B]; positivity
  have hRB : R/B ≤ p/2 := by
    apply (div_le_iff₀ hB).2
    dsimp [B]
    rw [show p/2*(1+2*R/p) = p/2+R by field_simp]
    linarith
  have hlg := Real.log_le_sub_one_of_pos (div_pos hx hB)
  rw [Real.log_div hx.ne' hB.ne'] at hlg
  have hl := mul_le_mul_of_nonneg_left hlg hR
  have hr := mul_le_mul_of_nonneg_right hRB hx.le
  rw [div_mul_eq_mul_div] at hr
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change Real.log x*R + -p*x ≤ R*Real.log B + -(p/2)*x
  nlinarith [show R*(x/B) = R*x/B by ring]

theorem mellin_exp_tail_bound (g : ℝ → ℂ) (hg : Measurable g)
    (hzero : ∀ x ≤ 1, g x = 0) {p C R : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbound : ∀ x : ℝ, 1 < x → ‖g x‖ ≤ C * Real.exp (-p*x))
    (s : ℂ) (hs : s.re - 1 ≤ R) :
    MellinConvergent g s ∧
      ‖mellin g s‖ ≤ (C * Real.exp (R*Real.log (1+2*R/p))) * (2/p) := by
  let D := fun x : ℝ => (C * Real.exp (R*Real.log (1+2*R/p))) * Real.exp (-(p/2)*x)
  have hD : IntegrableOn D (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(p/2)<0) 0).const_mul _
  have hD0 (x : ℝ) : 0 ≤ D x := by dsimp [D]; positivity
  have hpt : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(x : ℂ)^(s-1) • g x‖ ≤ D x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    by_cases h : 1 < x
    · rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.sub_re, Complex.one_re]
      calc
        _ ≤ x^R * (C*Real.exp (-p*x)) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le h.le hs) (hbound x h)
            (norm_nonneg _) (Real.rpow_nonneg hx'.le _)
        _ = C * (x^R * Real.exp (-p*x)) := by ring
        _ ≤ D x := (mul_le_mul_of_nonneg_left (power_exp_majorant hp hR hx') hC).trans_eq (by
          unfold D; ring)
    · rw [hzero x (le_of_not_gt h), smul_zero, norm_zero]
      exact hD0 x
  refine ⟨?_, ?_⟩
  · have hm : ContinuousOn (fun x : ℝ => (x : ℂ)^(s-1)) (Set.Ioi 0) :=
      continuousOn_of_forall_continuousAt fun x hx =>
        Complex.continuousAt_ofReal_cpow_const x (s-1) (Or.inr (ne_of_gt (show 0 < x from hx)))
    exact hD.mono' ((hm.aestronglyMeasurable measurableSet_Ioi).smul hg.aestronglyMeasurable) hpt
  · calc
      _ ≤ ∫ x in Set.Ioi (0 : ℝ), D x := norm_integral_le_of_norm_le hD hpt
      _ ≤ _ := by
        unfold D
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(p/2)<0)]
        simp

end RHConnections.SpectralTail
