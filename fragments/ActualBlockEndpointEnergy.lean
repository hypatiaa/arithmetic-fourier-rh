import Verified
import BlockEndpointBounds
import ActualBlockEnergySmoothing

namespace RHConnections.BlockFourier

open RHConnections.RankPairing ArithmeticFourierMertensKernel
variable {J : ℕ} [NeZero J]

theorem rank_pair_energy_of_buthe_endpoints
    (N R : ℕ) (hR : 0 < R) (t : ℕ → ℕ) (ht : Antitone t)
    (u : ℕ → ℝ) (Q : ℝ) (hQ : 0≤Q)
    (hu0 : u 0=Q) (hu : ∀ j ≤ J, u j≤2*Q)
    (hf : ∀ j ≤ J, |Chebyshev.psi (u j)-u j|≤(94/100:ℝ)*Real.sqrt (u j)) :
    let F := fun j => Chebyshev.psi (u j)-u j
    let d : ZMod J → ℝ := fun j => F (j.val+1)-F j.val
    let K := blockCutoffKernel (smoothReal R d) t
    sqNorm N (fun n => K n-averageCorrection N K n) ≤ 25*(N:ℝ)*Q := by
  dsimp only
  let F := fun j => Chebyshev.psi (u j)-u j
  let d : ZMod J → ℝ := fun j => F (j.val+1)-F j.val
  let K := blockCutoffKernel (smoothReal R d) t
  have hstep (j : ℕ) (hj : j<J) : d (j:ZMod J)=F (j+1)-F j := by
    simp only [d,ZMod.val_natCast_of_lt hj]
  have hsmooth : ∀ a length, length ≤ J →
      |blockIntervalSum (smoothReal R d) a length| ≤ 5*Real.sqrt Q :=
    cyclic_interval_bound_preserved d (smoothingKernel R) (smoothing_kernel_nonneg R)
      (smoothing_kernel_mass hR) _
      (fun a length hlen => buthe_endpoint_interval_bound d F u Q hQ hstep hu0 hu hf a length hlen)
  have hn := rank_residual_of_interval_bound N t ht (smoothReal R d)
    (5*Real.sqrt Q) (by positivity) hsmooth
  change ‖residualVector N K‖ ≤ Real.sqrt (N:ℝ)*(5*Real.sqrt Q) at hn
  rw [norm_rank_residual] at hn
  change sqNorm N (fun n => K n-averageCorrection N K n) ≤ _
  have hp : 0≤sqNorm N (fun n => K n-averageCorrection N K n) := by
    exact sqNorm_nonneg N _
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  rw [Real.sq_sqrt hp,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt hQ] at hh
  exact hh.trans_eq (by ring)

end RHConnections.BlockFourier
