import Verified
import RankCenteredContrast

noncomputable section
namespace RHConnections.RankContrast

variable {ι : Type*}

theorem difference_of_group_means (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
    (v : ι → ℂ) :
    mean A v - mean B v =
      (∑ i∈A, ∑ j∈B,(v i-v j))/((A.card:ℂ)*(B.card:ℂ)) := by
  have ha : (A.card:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  have hb : (B.card:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hB)
  simp only [mean,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
  field_simp

theorem lower_group_contrast (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
    (v : ι → ℂ) (rotation : ℂ) (d : ℝ)
    (hl : ∀ i∈A, ∀ j∈B, d≤(rotation*(v i-v j)).re) :
    d≤(rotation*(mean A v-mean B v)).re := by
  rw [difference_of_group_means A B hA hB]
  have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
  have hb : (0:ℝ)<B.card := by exact_mod_cast hB.card_pos
  have he : (rotation * (∑ i ∈ A, ∑ j ∈ B, (v i-v j)) /
      ((A.card:ℂ)*(B.card:ℂ))).re =
      (∑ i∈A,∑ j∈B, (rotation*(v i-v j)).re)/((A.card:ℝ)*(B.card:ℝ)) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    have hcast : ((A.card:ℂ)*(B.card:ℂ))=(((A.card:ℝ)*(B.card:ℝ):ℝ):ℂ) := by norm_cast
    rw [hcast,Complex.div_ofReal_re]
    change Complex.reCLM (∑ i∈A,∑ j∈B,rotation*(v i-v j)) / _ = _
    simp only [map_sum,Complex.reCLM_apply]

  have hreal : d*((A.card:ℝ)*(B.card:ℝ)) ≤ ∑ i∈A,∑ j∈B,(rotation*(v i-v j)).re := by
    calc
      _ = ∑ _i∈A,∑ _j∈B,d := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hl i hi))
  rw [←mul_div_assoc,he]
  exact (le_div_iff₀ (mul_pos ha hb)).mpr hreal

end RHConnections.RankContrast
