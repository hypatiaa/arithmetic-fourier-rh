import Verified
import RankCenteredContrast

noncomputable section
namespace RHConnections.RankContrast

variable {ι : Type*}

theorem contrast_add (A B : Finset ι) (length : ι → ℝ) (v w : ι → ℂ) :
    contrast A B length (fun i => v i+w i) =
      contrast A B length v + contrast A B length w := by
  simp only [contrast,mean,add_div,Finset.sum_add_distrib]
  ring

theorem contrast_length_multiple (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
    (length : ι → ℝ) (hpos : ∀ i, i∈A ∨ i∈B → 0<length i) (c : ℂ) :
    contrast A B length (fun i => c*(length i:ℂ))=0 := by
  have hmean (s : Finset ι) (hs : s.Nonempty) (hl : ∀ i∈s, 0<length i) :
      mean s (fun i => (c*(length i:ℂ))/(length i:ℂ))=c := by
    unfold mean
    rw [Finset.sum_congr rfl (fun i hi => mul_div_cancel_right₀ c
      (Complex.ofReal_ne_zero.mpr (hl i hi).ne')),Finset.sum_const,nsmul_eq_mul]
    exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs))
  unfold contrast
  rw [hmean A hA (fun i hi => hpos i (Or.inl hi)),hmean B hB (fun i hi => hpos i (Or.inr hi)),sub_self]

theorem contrast_uniform_error (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
    (length : ι → ℝ) (v : ι → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (hlen : ∀ i, i∈A ∨ i∈B → L≤length i)
    (herr : ∀ i, i∈A ∨ i∈B → ‖v i‖≤E) :
    ‖contrast A B length v‖≤2*E/L := by
  have hmean (s : Finset ι) (hs : s.Nonempty) (hl : ∀ i∈s, L≤length i)
      (he : ∀ i∈s, ‖v i‖≤E) : ‖mean s (fun i => v i/(length i:ℂ))‖≤E/L := by
    have hcard : (0:ℝ)<s.card := by exact_mod_cast hs.card_pos
    rw [mean,norm_div,Complex.norm_natCast]
    calc
      _ ≤ (∑ _i∈s,E/L)/(s.card:ℝ) := by
        apply div_le_div_of_nonneg_right _ hcard.le
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hL.trans_le (hl i hi))]
        exact (div_le_div_of_nonneg_right (he i hi) (hL.trans_le (hl i hi)).le).trans
          (div_le_div_of_nonneg_left hE hL (hl i hi))
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        exact mul_div_cancel_left₀ _ hcard.ne'
  exact ((norm_sub_le _ _).trans (add_le_add
    (hmean A hA (fun i hi => hlen i (Or.inl hi)) (fun i hi => herr i (Or.inl hi)))
    (hmean B hB (fun i hi => hlen i (Or.inr hi)) (fun i hi => herr i (Or.inr hi))))).trans_eq (by ring)

theorem contrast_transfer_of_length_error {A B rows : Finset ι}
    (hA : A.Nonempty) (hB : B.Nonempty) (ha : A⊆rows) (hb : B⊆rows)
    (physical grid : ι → ℝ) (v w : ι → ℂ) (c : ℂ) (scale : ℝ)
    {L E W : ℝ} (hL : 0<L) (hE : 0≤E) (hW : 0≤W)
    (hlen : ∀ i, i∈A ∨ i∈B → L≤physical i)
    (hval : ∀ i, i∈A ∨ i∈B → ‖w i-v i‖≤E)
    (hwidth : ∀ i, i∈A ∨ i∈B → |grid i-scale*physical i|≤W) :
    ‖contrast A B physical w‖ ≤
      Real.sqrt (∑ i∈rows,‖v i-c*(grid i:ℂ)‖^2) *
        ((Real.sqrt (A.card:ℝ)*L)⁻¹+(Real.sqrt (B.card:ℝ)*L)⁻¹) +
      2*(E+‖c‖*W)/L := by
  let D (i : ι) := v i-c*(grid i:ℂ)
  let err (i : ι) := w i-v i+c*((grid i-scale*physical i:ℝ):ℂ)
  have hdecomp : w=(fun i => (D i+err i)+(c*(scale:ℂ))*(physical i:ℂ)) := by
    ext i
    simp only [D,err,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  have hsum :
      contrast A B physical w=contrast A B physical D+contrast A B physical err := by
    conv_lhs => rw [hdecomp]
    rw [contrast_add,contrast_add,contrast_length_multiple A B hA hB physical
      (fun i hi => hL.trans_le (hlen i hi)),add_zero]
  rw [hsum]
  have hD := centered_contrast_le hA hB ha hb physical D 0 hL
    (fun i hi => hlen i (Or.inl hi)) (fun i hi => hlen i (Or.inr hi))
  have he (i) (hi : i∈A ∨ i∈B) : ‖err i‖≤E+‖c‖*W := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact add_le_add (hval i hi) (mul_le_mul_of_nonneg_left (hwidth i hi) (norm_nonneg _))
  have her := contrast_uniform_error A B hA hB physical err hL
    (show 0≤E+‖c‖*W by positivity) hlen he
  exact (norm_add_le _ _).trans (add_le_add (by simpa [D] using hD) her)

end RHConnections.RankContrast
