import Verified
import FinitePerronRectangle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory Set Complex

namespace RHConnections.FinitePerron

theorem integral_tails_bound {g : ℝ → ℂ} (hg : Integrable g) {T D : ℝ}
    (hT : 0<T) (hD : 0≤D)
    (hbound : ∀ t, T≤|t| → ‖g t‖ ≤ D*|t|^(-2:ℝ)) :
    ‖(∫ t : ℝ, g t) - ∫ t in -T..T, g t‖ ≤ 2*D/T := by
  let f (t : ℝ) := D*t^(-2:ℝ)
  have hRightInt : IntegrableOn f (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hT).const_mul _
  have hRightValue : (∫ t in Ioi T, f t) = D/T := by
    dsimp [f]
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hT]
    norm_num
    rw [Real.rpow_neg_one]
    ring
  let negM : ℝ → ℝ := fun t => -t
  have hNeg : MeasurePreserving negM volume volume := Measure.measurePreserving_neg _
  have hEmb : MeasurableEmbedding negM := (Homeomorph.neg ℝ).measurableEmbedding
  have hNegSet : negM ⁻¹' Ioi T = Iio (-T) := by ext t; simp [negM]
  have hLeftValue : (∫ t in Iio (-T), f (-t)) = D/T := by
    rw [←hNegSet]
    exact (hNeg.setIntegral_preimage_emb hEmb f _).trans hRightValue
  have hLeftInt : IntegrableOn (fun t => f (-t)) (Iio (-T)) := by
    rw [←hNegSet]
    exact (hNeg.integrableOn_comp_preimage hEmb).mpr hRightInt
  have hr : ‖∫ t in Ioi T, g t‖≤D/T := by
    rw [←hRightValue]
    apply norm_integral_le_of_norm_le hRightInt
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun t ht => by
      have hp : 0<t := hT.trans ht
      simpa only [f,abs_of_pos hp] using hbound t (by rw [abs_of_pos hp]; exact (show T < t from ht).le)))
  have hl : ‖∫ t in Iio (-T), g t‖≤D/T := by
    rw [←hLeftValue]
    apply norm_integral_le_of_norm_le hLeftInt
    exact (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ (fun t ht => by
      have hn : t<0 := (show t < -T from ht).trans (neg_neg_of_pos hT)
      simpa only [f,abs_of_neg hn] using hbound t (by rw [abs_of_neg hn]; linarith only [show t < -T from ht])))
  have hc : (∫ t in Icc (-T) T, g t) = ∫ t in -T..T, g t := by
    rw [intervalIntegral.integral_of_le (by linarith : -T≤T), integral_Icc_eq_integral_Ioc]
  have hsplit : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext t
    simp only [Set.mem_compl_iff,Set.mem_Icc,Set.mem_union,Set.mem_Iio,Set.mem_Ioi,not_and_or,not_le]
  have hdis : Disjoint (Iio (-T)) (Ioi T) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    have h₁ : t < -T := ht
    have h₂ : T < t := ht'
    linarith
  have he := integral_add_compl measurableSet_Icc hg (s := Icc (-T) T)
  rw [hc,hsplit,setIntegral_union hdis measurableSet_Ioi hg.integrableOn hg.integrableOn] at he
  rw [←he,add_sub_cancel_left]
  exact ((norm_add_le _ _).trans (add_le_add hl hr)).trans_eq (by ring)

end RHConnections.FinitePerron
