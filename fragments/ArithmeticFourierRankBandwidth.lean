import Verified
import ArithmeticFourierRankGram

open scoped RealInnerProductSpace
noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierInversion ArithmeticFourierMertensKernel

def indexBand (r w i : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun j => i ≤ j+w ∧ j ≤ i+w)

theorem index_band_card (r w i : ℕ) : (indexBand r w i).card ≤ 2*w+1 := by
  have hs : indexBand r w i ⊆ Finset.Icc (i-w) (i+w) := by
    intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  omega

private theorem sum_squares_over_bands (r w : ℕ) (d : ℕ → ℝ) :
    (∑ i ∈ Finset.range r,∑ j ∈ indexBand r w i,((d i)^2+(d j)^2)) =
      2*∑ i ∈ Finset.range r,(indexBand r w i).card*(d i)^2 := by
  have hswap : (∑ i ∈ Finset.range r,∑ j ∈ indexBand r w i,(d j)^2) =
      ∑ i ∈ Finset.range r,∑ j ∈ indexBand r w i,(d i)^2 := by
    unfold indexBand
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      simp only [and_comm]))
  simp_rw [Finset.sum_add_distrib]
  rw [hswap]
  simp_rw [Finset.sum_const,nsmul_eq_mul]
  ring

theorem weighted_gram_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℕ) (V : ℕ → E) (d : ℕ → ℝ) :
    ‖∑ j ∈ Finset.range r,d j • V j‖^2 =
      ∑ i ∈ Finset.range r,∑ j ∈ Finset.range r,d i*d j*⟪V i,V j⟫ := by
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  simp only [inner_sum,real_inner_smul_left,real_inner_smul_right]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem orthogonal_weighted_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℕ) (V : ℕ → E) (d : ℕ → ℝ)
    (h : ∀ i<r, ∀ j<r, i≠j → ⟪V i,V j⟫=0) :
    ‖∑ j ∈ Finset.range r,d j • V j‖^2 =
      ∑ i ∈ Finset.range r,(d i)^2*‖V i‖^2 := by
  rw [weighted_gram_expansion]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq,pow_two (d i)]
  · intro j hj hji
    rw [h i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hji.symm,mul_zero]
  · intro hn
    exact (hn hi).elim

theorem banded_gram_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r w : ℕ) (V : ℕ → E) (d : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (hV : ∀ i<r, ‖V i‖^2 ≤ B)
    (hzero : ∀ i<r, ∀ j<r, j∉indexBand r w i → ⟪V i,V j⟫=0) :
    ‖∑ j ∈ Finset.range r,d j • V j‖^2 ≤
      B*(2*(w:ℝ)+1)*(∑ j ∈ Finset.range r,(d j)^2) := by
  have hterm (i j : ℕ) (hi : i<r) (hj : j<r) :
      d i*d j*⟪V i,V j⟫ ≤ B*((d i)^2+(d j)^2)/2 := by
    have hnorm (k : ℕ) (hk : k<r) : ‖V k‖ ≤ Real.sqrt B :=
      (Real.le_sqrt (norm_nonneg _) hB).mpr (hV k hk)
    have hinner : |⟪V i,V j⟫| ≤ B := by
      apply (abs_real_inner_le_norm _ _).trans
      have hh := mul_le_mul (hnorm i hi) (hnorm j hj) (norm_nonneg _) (Real.sqrt_nonneg _)
      rwa [← pow_two,Real.sq_sqrt hB] at hh
    have hAM : |d i| * |d j| ≤ ((d i)^2+(d j)^2)/2 := by
      have hh := sq_nonneg (|d i|-|d j|)
      nlinarith only [hh,sq_abs (d i),sq_abs (d j)]
    calc
      _ ≤ |d i*d j*⟪V i,V j⟫| := le_abs_self _
      _ = |d i| * |d j| * |⟪V i,V j⟫| := by rw [abs_mul,abs_mul]
      _ ≤ |d i| * |d j| * B := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_right hAM hB).trans_eq (by ring)
  calc
    _ = ∑ i ∈ Finset.range r,∑ j ∈ indexBand r w i,d i*d j*⟪V i,V j⟫ := by
      rw [weighted_gram_expansion]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) (fun j hj hjnot => ?_)
      rw [hzero i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hjnot,mul_zero]
    _ ≤ ∑ i ∈ Finset.range r,∑ j ∈ indexBand r w i,B*((d i)^2+(d j)^2)/2 := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
      exact hterm i j (Finset.mem_range.mp hi) (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    _ = B*∑ i ∈ Finset.range r,(indexBand r w i).card*(d i)^2 := by
      have he (i j : ℕ) : B*((d i)^2+(d j)^2)/2 = (B/2)*((d i)^2+(d j)^2) := by ring
      simp only [he,← Finset.mul_sum]
      rw [sum_squares_over_bands r w d]
      ring
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hB
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h := index_band_card r w i
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)

theorem residual_inner_eq_dot (N : ℕ) (K L : ℕ → ℝ) :
    ⟪residualVector N K,residualVector N L⟫ =
      dot N (actualResidual N K) (actualResidual N L) := by
  classical
  rw [PiLp.inner_apply]
  simp only [residualVector,LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_toLp,Real.inner_apply,dot,actualResidual]
  exact (Finset.sum_subtype (Finset.Ioc (0:ℕ) N) (fun _ => Iff.rfl)
    (fun n : ℕ => (K n-averageCorrection N K n)*(L n-averageCorrection N L n))).symm

theorem rank_banded_cutoff_cost (N r w : ℕ) (t : ℕ → ℕ) (d : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (ht : ∀ j<r, t j≤N) (hM : ∀ j<r, |M (t j)|≤B)
    (hfar : ∀ i<r, ∀ j<r, j∉indexBand r w i →
      8*B+4*(N.sqrt:ℝ) ≤ ((max (t i) (t j)-min (t i) (t j):ℕ):ℝ)) :
    let K := fun n => ∑ j ∈ Finset.range r,d j*cutoffStep (t j) n
    sqNorm N (actualResidual N K) ≤
      B*(2*(w:ℝ)+1)*(∑ j ∈ Finset.range r,(d j)^2) := by
  let V := fun j => residualVector N (cutoffStep (t j))
  have hV (i : ℕ) (hi : i<r) : ‖V i‖^2 ≤ B := by
    dsimp [V]
    rw [norm_rank_residual,Real.sq_sqrt (sqNorm_nonneg _ _)]
    exact (rank_step_cost_le_mertens N (t i) (ht i hi)).trans (hM i hi)
  have hzero (i : ℕ) (hi : i<r) (j : ℕ) (hj : j<r) (hnot : j∉indexBand r w i) :
      ⟪V i,V j⟫=0 := by
    have hgap := hfar i hi j hj hnot
    rcases le_total (t i) (t j) with h₁|h₂
    · rw [max_eq_right h₁,min_eq_left h₁] at hgap
      dsimp [V]
      rw [residual_inner_eq_dot]
      exact actual_cutoff_gram_zero_of_spacing h₁ (ht j hj) (hM i hi) (hM j hj) hgap
    · rw [max_eq_left h₂,min_eq_right h₂] at hgap
      dsimp [V]
      rw [real_inner_comm,residual_inner_eq_dot]
      exact actual_cutoff_gram_zero_of_spacing h₂ (ht i hi) (hM j hj) (hM i hi) hgap
  have h := banded_gram_bound r w V d B hB hV hzero
  have he : (∑ j ∈ Finset.range r,d j • V j) =
      residualVector N (fun n => ∑ j ∈ Finset.range r,d j*cutoffStep (t j) n) := by
    have hfun : (fun n => ∑ j ∈ Finset.range r,d j*cutoffStep (t j) n) =
        ∑ j ∈ Finset.range r,d j • cutoffStep (t j) := by ext n; simp [Finset.sum_apply]
    rw [hfun,map_sum]
    simp only [map_smul,V]
  rw [he,norm_rank_residual,Real.sq_sqrt (sqNorm_nonneg _ _)] at h
  exact h

end RHConnections.RankPairing
