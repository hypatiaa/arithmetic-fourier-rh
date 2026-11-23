import Verified
import BlockJacksonSpectrum
import BlockDirichletMoments

namespace RHConnections.BlockFourier
open RHConnections.RankPairing
variable {J : ℕ} [NeZero J]

theorem jackson_circular_first_moment (R : ℕ) (hR : 0<R) (hRJ : R≤J) :
    (∑ h : ZMod J, smoothingKernel R h * (blockCyclicDistance h:ℝ)) ≤
      3*(J:ℝ)/(R:ℝ) := by
  let D (h : ZMod J) := ‖blockDirichletKernel R h‖
  let A := normalizingMass (J := J) R
  have hA : 0<A := normalizing_mass_positive hR
  have hJ : (0:ℝ)<J := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne J)
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have hsum2 : (∑ h,D h^2) = (J:ℝ)*R := block_dirichlet_second_moment R hRJ
  have hsum4 : (∑ h,D h^4) = A := rfl
  have hlower : (J:ℝ)*(R:ℝ)^3/27≤A := by
    rw [←hsum4]
    exact block_dirichlet_fourth_moment_lower R hR
  have hsquared : (∑ h,D h^3)^2 ≤ (J:ℝ)*R*A := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod J)) D (fun h => D h^2)
    have h3 (h) : D h * D h^2 = D h^3 := by ring
    have h4 (h) : (D h^2)^2 = D h^4 := by ring
    simpa only [h3,h4,hsum2,hsum4] using hh
  have hcube : (∑ h,D h^3) ≤ 6*A/R := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_left hsquared (sq_nonneg (R:ℝ))
    have hbound := mul_le_mul_of_nonneg_right hlower hA.le
    have hp : 0≤(∑ h,D h^3)*(R:ℝ) := by
      exact mul_nonneg (Finset.sum_nonneg fun h _ => pow_nonneg (norm_nonneg _) _) hr.le
    nlinarith [sq_nonneg ((∑ h,D h^3)*(R:ℝ)-6*A)]
  have he : (∑ h : ZMod J, smoothingKernel R h * (blockCyclicDistance h:ℝ)) =
      (∑ h : ZMod J, (blockCyclicDistance h:ℝ)*D h^4)/A := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h _
    change D h^4/A * _ = _
    ring
  rw [he]
  apply (div_le_iff₀ hA).mpr
  calc
    (∑ h : ZMod J, (blockCyclicDistance h:ℝ)*D h^4)
      ≤ ∑ h : ZMod J, ((J:ℝ)/2)*D h^3 := by
        apply Finset.sum_le_sum
        intro h _
        have hh := mul_le_mul_of_nonneg_right (block_dirichlet_kernel_bound R h)
          (pow_nonneg (norm_nonneg (blockDirichletKernel R h)) 3)
        change (_ * D h) * D h^3 ≤ _ at hh
        convert hh using 1
        ring
    _ = ((J:ℝ)/2)*(∑ h,D h^3) := by rw [Finset.mul_sum]
    _ ≤ ((J:ℝ)/2)*(6*A/R) := mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring

end RHConnections.BlockFourier
