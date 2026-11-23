import Verified

noncomputable section
namespace RHConnections.BlockFourier

variable {ι : Type*} [Fintype ι]

theorem weighted_pair_difference_identity (v h : ι → ℝ) :
    (∑ i, ∑ j, v i*v j*(h i-h j)^2) =
      2*((∑ i,v i)*(∑ i,v i*(h i)^2)-(∑ i,v i*h i)^2) := by
  calc
    _ = ∑ i, ∑ j,
        (v j*(v i*(h i)^2) + v i*(v j*(h j)^2) -
          2*(v i*h i)*(v j*h j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
      ring

theorem weighted_variance_by_pair_differences (v h : ι → ℝ)
    (hA : 0 < ∑ i, v i) :
    let A := ∑ i,v i
    let m := (∑ i,v i*h i)/A
    A*(∑ i,v i*(h i-m)^2) =
      (∑ i, ∑ j,v i*v j*(h i-h j)^2)/2 := by
  dsimp only
  let A := ∑ i,v i
  let S := ∑ i,v i*h i
  let m := S/A
  change A*(∑ i,v i*(h i-m)^2) = _
  have he : (∑ i,v i*(h i-m)^2) = (∑ i,v i*(h i)^2)+A*m^2-2*m*S := by
    calc
      _ = ∑ i,(v i*(h i)^2 + v i*m^2 - 2*m*(v i*h i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,A,S]
  rw [he,weighted_pair_difference_identity]
  change A*((∑ i,v i*(h i)^2)+A*m^2-2*m*S) =
    2*(A*(∑ i,v i*(h i)^2)-S^2)/2
  have hA0 : A ≠ 0 := hA.ne'
  dsimp [m]
  field_simp [hA0]
  <;> ring

end RHConnections.BlockFourier
