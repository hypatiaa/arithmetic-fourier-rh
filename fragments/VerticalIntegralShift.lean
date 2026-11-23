import Verified
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace RHConnections.VerticalIntegralShift
open Complex MeasureTheory Filter Set
open scoped Topology Interval

private theorem horizontal_limit {F : ℂ → ℂ} {b c : ℝ} (hbc : b ≤ c)
    (height A : ℝ → ℝ) (hA : Tendsto A atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop, ∀ x ∈ Icc b c, ‖F ((x:ℂ) + (height T:ℂ)*I)‖ ≤ A T) :
    Tendsto (fun T => ∫ x in b..c, F ((x:ℂ) + (height T:ℂ)*I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun T => A T * |c-b|)
  · filter_upwards [hbound] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hbc] at hx
    exact hT x ⟨hx.1.le,hx.2⟩
  · simpa using hA.mul_const |c-b|

theorem vertical_integral_eq {F : ℂ → ℂ} {b c : ℝ} (hbc : b ≤ c)
    (hF : AnalyticOnNhd ℂ F {z | z.re ∈ Icc b c})
    (hb : Integrable fun t : ℝ => F ((b:ℂ)+(t:ℂ)*I))
    (hc : Integrable fun t : ℝ => F ((c:ℂ)+(t:ℂ)*I))
    (A : ℝ → ℝ) (hA : Tendsto A atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop, ∀ x ∈ Icc b c,
      ‖F ((x:ℂ)+((-T:ℝ):ℂ)*I)‖ ≤ A T ∧ ‖F ((x:ℂ)+(T:ℂ)*I)‖ ≤ A T) :
    (∫ t : ℝ, F ((b:ℂ)+(t:ℂ)*I)) = ∫ t : ℝ, F ((c:ℂ)+(t:ℂ)*I) := by
  have hlow := horizontal_limit (F := F) hbc (fun T => -T) A hA
    (hbound.mono fun T h x hx => (h x hx).1)
  have hhigh := horizontal_limit (F := F) hbc id A hA
    (hbound.mono fun T h x hx => (h x hx).2)
  have hl := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hr := intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id
  have H := (((hlow.sub hhigh).add (hr.const_mul I)).sub (hl.const_mul I))
  have E (T : ℝ) := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ⟨b,-T⟩ ⟨c,T⟩ (fun z hz => (hF z (by
      change z.re ∈ Icc b c
      exact (uIcc_of_le hbc) ▸ hz.1)).differentiableAt.differentiableWithinAt)
  have Z := tendsto_nhds_unique H (tendsto_const_nhds.congr
    (fun T : ℝ => (E T).symm))
  simp only [sub_self, zero_add, sub_eq_zero] at Z
  exact (mul_left_cancel₀ I_ne_zero Z).symm

end RHConnections.VerticalIntegralShift
