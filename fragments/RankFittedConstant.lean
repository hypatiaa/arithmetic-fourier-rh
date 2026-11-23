import Verified

noncomputable section
namespace RHConnections.RankContrast

variable {ι : Type*} [Fintype ι]

def fittedConstant (w length v : ι → ℝ) : ℝ :=
  (∑ i,w i*length i*v i)/(∑ i,w i*(length i)^2)

def centeredEnergy (w length v : ι → ℝ) (c : ℝ) : ℝ :=
  ∑ i,w i*(v i-c*length i)^2

theorem fitted_constant_identity (w length v : ι → ℝ) (c : ℝ)
    (hA : 0<∑ i,w i*(length i)^2) :
    centeredEnergy w length v c =
      centeredEnergy w length v (fittedConstant w length v) +
      (c-fittedConstant w length v)^2*(∑ i,w i*(length i)^2) := by
  let d := fittedConstant w length v
  let A := ∑ i,w i*(length i)^2
  let S := ∑ i,w i*length i*v i
  have hAd : d*A=S := by
    change S/A*A=S
    exact div_mul_cancel₀ _ hA.ne'
  have hzero : (∑ i,w i*length i*(v i-d*length i))=0 := by
    have he (i : ι) : w i*length i*(v i-d*length i)=
        w i*length i*v i-d*(w i*(length i)^2) := by ring
    simp only [he,Finset.sum_sub_distrib,←Finset.mul_sum]
    change S-d*A=0
    rw [hAd,sub_self]
  change centeredEnergy w length v c = centeredEnergy w length v d + (c-d)^2*A
  unfold centeredEnergy
  calc
    _ = ∑ i,(w i*(v i-d*length i)^2 + (c-d)^2*(w i*(length i)^2) -
         (2*(c-d))*(w i*length i*(v i-d*length i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
      hzero,mul_zero,sub_zero,A]

theorem fitted_constant_minimizes (w length v : ι → ℝ) (c : ℝ)
    (hA : 0<∑ i,w i*(length i)^2) :
    centeredEnergy w length v (fittedConstant w length v) ≤ centeredEnergy w length v c := by
  rw [fitted_constant_identity w length v c hA]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hA.le)

theorem fitted_constant_bound (w length v : ι → ℝ) {D : ℝ}
    (hw : ∀ i, 0≤w i) (hl : ∀ i, 0≤length i)
    (hA : 0<∑ i,w i*(length i)^2) (hv : ∀ i, |v i|≤D*length i) :
    |fittedConstant w length v|≤D := by
  rw [fittedConstant,abs_div,abs_of_pos hA]
  apply (div_le_iff₀ hA).mpr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ i, D*(w i*(length i)^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (mul_nonneg (hw i) (hl i))]
      exact (mul_le_mul_of_nonneg_left (hv i) (mul_nonneg (hw i) (hl i))).trans_eq (by ring)
    _ = _ := by rw [Finset.mul_sum]

end RHConnections.RankContrast
