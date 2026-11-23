import Verified
import RankFittedConstant

noncomputable section
namespace RHConnections.RankContrast
variable {ι : Type*} [Fintype ι]

def weightedRowVector (w v : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (w i)*v i)

theorem norm_weighted_row (w v : ι → ℝ) (hw : ∀ i, 0≤w i) :
    ‖weightedRowVector w v‖ = Real.sqrt (∑ i,w i*(v i)^2) := by
  simp only [weightedRowVector, PiLp.norm_eq_of_L2,Real.norm_eq_abs,sq_abs,mul_pow,
    Real.sq_sqrt (hw _)]

def centeredDistance (w length v : ι → ℝ) : ℝ :=
  Real.sqrt (centeredEnergy w length v (fittedConstant w length v))

theorem centered_distance_one_direction (w length v u : ι → ℝ)
    (hw : ∀ i,0≤w i) (hA : 0<∑ i,w i*(length i)^2) :
    centeredDistance w length v ≤
      ‖weightedRowVector w (fun i => v i-u i)‖+centeredDistance w length u := by
  let c := fittedConstant w length u
  have hd : weightedRowVector w (fun i => v i-c*length i) =
      weightedRowVector w (fun i => v i-u i)+weightedRowVector w (fun i => u i-c*length i) := by
    ext i
    change Real.sqrt (w i)*(v i-c*length i) =
      Real.sqrt (w i)*(v i-u i)+Real.sqrt (w i)*(u i-c*length i)
    ring
  refine (Real.sqrt_le_sqrt (fitted_constant_minimizes w length v c hA)).trans ?_
  rw [show Real.sqrt (centeredEnergy w length v c)=
      ‖weightedRowVector w (fun i => v i-c*length i)‖ by rw [norm_weighted_row w _ hw]; rfl,hd]
  refine (norm_add_le _ _).trans_eq ?_
  simp only [norm_weighted_row w _ hw]
  rfl

theorem centered_distance_lipschitz (w length v u : ι → ℝ)
    (hw : ∀ i,0≤w i) (hA : 0<∑ i,w i*(length i)^2) :
    |centeredDistance w length v-centeredDistance w length u| ≤
      Real.sqrt (∑ i,w i*(v i-u i)^2) := by
  apply abs_sub_le_iff.mpr
  have h₁ := centered_distance_one_direction w length v u hw hA
  have h₂ := centered_distance_one_direction w length u v hw hA
  rw [norm_weighted_row w _ hw] at h₁ h₂
  have he (i : ι) : (u i-v i)^2=(v i-u i)^2 := by ring
  simp only [he] at h₂
  exact ⟨by linarith only [h₁],by linarith only [h₂]⟩

theorem centered_distance_uniform_error (w length v u : ι → ℝ)
    (hw : ∀ i,0≤w i) (hA : 0<∑ i,w i*(length i)^2)
    (N E : ℝ) (hN : 0≤N) (hE : 0≤E)
    (hs : ∑ i,w i ≤ N) (he : ∀ i, |v i-u i|≤E) :
    |centeredDistance w length v-centeredDistance w length u|≤Real.sqrt N*E := by
  apply (centered_distance_lipschitz w length v u hw hA).trans
  have hsq : (∑ i,w i*(v i-u i)^2)≤N*E^2 := by
    calc
      _ ≤ ∑ i,w i*E^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [←sq_abs (v i-u i)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (he i) _) (hw i)
      _ = (∑ i,w i)*E^2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  exact (Real.sqrt_le_sqrt hsq).trans_eq (by rw [Real.sqrt_mul hN,Real.sqrt_sq hE])

end RHConnections.RankContrast
