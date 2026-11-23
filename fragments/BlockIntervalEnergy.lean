import Verified
import BlockIntervalShift

noncomputable section
namespace RHConnections.BlockFourier
open RHConnections.RankPairing

variable {J : ℕ} [NeZero J] {ι : Type*} [Fintype ι]

def intervalEnergy (a : ι → ZMod J) (length : ι → ℕ) (w : ι → ℝ)
    (d : ZMod J → ℝ) : ℝ :=
  ∑ i, w i*(blockIntervalSum d (a i) (length i))^2

private def intervalVector (a : ι → ZMod J) (length : ι → ℕ) (w : ι → ℝ)
    (d : ZMod J → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (w i)*blockIntervalSum d (a i) (length i))

private theorem interval_vector_norm (a : ι → ZMod J) (length : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i, 0≤w i) (d : ZMod J → ℝ) :
    ‖intervalVector a length w d‖ = Real.sqrt (intervalEnergy a length w d) := by
  rw [PiLp.norm_eq_of_L2]
  apply congrArg Real.sqrt
  unfold intervalEnergy
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [intervalVector,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt (hw i)]

private theorem interval_vector_sub (a : ι → ZMod J) (length : ι → ℕ) (w : ι → ℝ)
    (d e : ZMod J → ℝ) :
    intervalVector a length w (d-e) = intervalVector a length w d-intervalVector a length w e := by
  ext i
  change Real.sqrt (w i)*blockIntervalSum (d-e) (a i) (length i) =
    Real.sqrt (w i)*blockIntervalSum d (a i) (length i)-
      Real.sqrt (w i)*blockIntervalSum e (a i) (length i)
  simp only [blockIntervalSum,Pi.sub_apply,Finset.sum_sub_distrib,mul_sub]

theorem smoothing_error_energy_bound (a : ι → ZMod J) (length : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i, 0≤w i) (d L : ZMod J → ℝ) (H N : ℝ) (hH : 0≤H) (hN : 0≤N)
    (hd : ∀ x, |d x|≤H) (hwN : ∑ i,w i≤N) (hL : ∑ h,L h=1) :
    let low := fun x => ∑ h,L h*d (x+h)
    let K := ∑ h,|L h| * (blockCyclicDistance h:ℝ)
    |Real.sqrt (intervalEnergy a length w d)-Real.sqrt (intervalEnergy a length w low)| ≤
      Real.sqrt N*(2*H*K) := by
  let low := fun x => ∑ h,L h*d (x+h)
  let K := ∑ h,|L h| * (blockCyclicDistance h:ℝ)
  have hK : 0≤K := Finset.sum_nonneg (fun h _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hT : 0≤2*H*K := by positivity
  have hrow (i : ι) : |blockIntervalSum (d-low) (a i) (length i)|≤2*H*K := by
    exact block_interval_smoothing d L H hd hL (a i) (length i)
  change |_ - Real.sqrt (intervalEnergy a length w low)| ≤ _
  rw [← interval_vector_norm a length w hw d,← interval_vector_norm a length w hw low]
  apply (abs_norm_sub_norm_le _ _).trans
  rw [← interval_vector_sub,interval_vector_norm a length w hw]
  have henergy : intervalEnergy a length w (d-low) ≤ N*(2*H*K)^2 := by
    unfold intervalEnergy
    calc
      _ ≤ ∑ i, w i*(2*H*K)^2 := by
        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i))
        rw [← sq_abs (blockIntervalSum (d-low) (a i) (length i))]
        exact pow_le_pow_left₀ (abs_nonneg _) (hrow i) _
      _ = _ * (2*H*K)^2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hwN (sq_nonneg _)
  exact (Real.sqrt_le_sqrt henergy).trans_eq (by rw [Real.sqrt_mul hN,Real.sqrt_sq hT])

end RHConnections.BlockFourier
