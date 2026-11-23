import Verified
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open MeasureTheory Set Complex
open scoped Interval

namespace RHConnections.FinitePerron

theorem central_vertical_bound {F : ℂ → ℂ} {b c T A B : ℝ}
    (hbc : b≤c) (hT : 0≤T)
    (hF : AnalyticOnNhd ℂ F {z | z.re ∈ Icc b c ∧ z.im ∈ Icc (-T) T})
    (hA : ∀ t ∈ Icc (-T) T, ‖F ((b:ℂ)+(t:ℂ)*I)‖≤A)
    (hB : ∀ x ∈ Icc b c,
      ‖F ((x:ℂ)+((-T:ℝ):ℂ)*I)‖≤B ∧ ‖F ((x:ℂ)+(T:ℝ)*I)‖≤B) :
    ‖∫ t in -T..T, F ((c:ℂ)+(t:ℂ)*I)‖ ≤ 2*T*A+2*(c-b)*B := by
  let iB := ∫ t in -T..T, F ((b:ℂ)+(t:ℂ)*I)
  let iC := ∫ t in -T..T, F ((c:ℂ)+(t:ℂ)*I)
  let bot := ∫ x in b..c, F ((x:ℂ)+((-T:ℝ):ℂ)*I)
  let top := ∫ x in b..c, F ((x:ℂ)+(T:ℝ)*I)
  have he := integral_boundary_rect_eq_zero_of_differentiableOn F
    ⟨b,-T⟩ ⟨c,T⟩ (fun z hz => (hF z (by
      change z.re ∈ Icc b c ∧ z.im ∈ Icc (-T) T
      exact ⟨(uIcc_of_le hbc) ▸ hz.1, (uIcc_of_le (by linarith : -T≤T)) ▸ hz.2⟩)).differentiableAt.differentiableWithinAt)
  change bot-top+I*iC-I*iB=0 at he
  have hrect : I*iC = I*iB+(top-bot) := by linear_combination he
  have hnorm (u v K : ℝ) (huv : u≤v) (f : ℝ → ℂ) (hf : ∀ x ∈ Icc u v, ‖f x‖≤K) :
      ‖∫ x in u..v, f x‖ ≤ K*|v-u| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le huv] at hx
    exact hf x ⟨hx.1.le,hx.2⟩
  have hlow : ‖bot‖ ≤ B*(c-b) := by
    rw [←abs_of_nonneg (sub_nonneg.mpr hbc)]
    exact hnorm _ _ _ hbc _ (fun x hx => (hB x hx).1)
  have hhigh : ‖top‖ ≤ B*(c-b) := by
    rw [←abs_of_nonneg (sub_nonneg.mpr hbc)]
    exact hnorm _ _ _ hbc _ (fun x hx => (hB x hx).2)
  have hl : ‖iB‖ ≤ A*(2*T) := by
    rw [show 2*T = |T-(-T)| by rw [abs_of_nonneg (by linarith)]; ring]
    exact hnorm _ _ _ (by linarith) _ hA
  change ‖iC‖≤_
  calc
    ‖iC‖ = ‖I*iC‖ := by simp
    _ = ‖I*iB+(top-bot)‖ := by rw [hrect]
    _ ≤ ‖iB‖+(‖top‖+‖bot‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add le_rfl (norm_sub_le top bot)
    _ ≤ _ := by linarith

end RHConnections.FinitePerron
