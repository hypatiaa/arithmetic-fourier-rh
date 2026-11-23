import Verified
import RadixActualRankPairing
import MixedRadix

noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierInversion ArithmeticFourierMertensKernel

private theorem average_add (N : ℕ) (K L : ℕ → ℝ) (n : ℕ) :
    averageCorrection N (K+L) n = averageCorrection N K n+averageCorrection N L n := by
  unfold averageCorrection
  split_ifs <;> dsimp only [Pi.add_apply] <;> (try split_ifs) <;> ring

private theorem average_smul (N : ℕ) (c : ℝ) (K : ℕ → ℝ) (n : ℕ) :
    averageCorrection N (c • K) n = c*averageCorrection N K n := by
  unfold averageCorrection
  split_ifs <;> dsimp only [Pi.smul_apply,smul_eq_mul] <;> (try split_ifs) <;> ring

abbrev RankCarrier (N : ℕ) := ↥(Finset.Ioc (0:ℕ) N)

def residualVector (N : ℕ) : (ℕ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (RankCarrier N) where
  toFun := fun K => WithLp.toLp 2 (fun n : RankCarrier N => K n-averageCorrection N K n)
  map_add' := by
    intro K L
    ext n
    change (K+L) n - averageCorrection N (K+L) n =
      (K n-averageCorrection N K n)+(L n-averageCorrection N L n)
    rw [average_add,Pi.add_apply]
    ring
  map_smul' := by
    intro c K
    ext n
    change (c • K) n - averageCorrection N (c • K) n =
      c*(K n-averageCorrection N K n)
    rw [average_smul,Pi.smul_apply,smul_eq_mul]
    ring

theorem norm_rank_residual (N : ℕ) (K : ℕ → ℝ) :
    ‖residualVector N K‖ = Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n)) := by
  classical
  rw [PiLp.norm_eq_of_L2]
  simp only [residualVector,LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_toLp,
    Real.norm_eq_abs,sq_abs,sqNorm,dot]
  simp only [pow_two]
  apply congrArg Real.sqrt
  exact (Finset.sum_subtype (Finset.Ioc (0:ℕ) N) (fun _ => Iff.rfl)
    (fun n : ℕ => (K n-averageCorrection N K n)*(K n-averageCorrection N K n))).symm

theorem rank_aggregate_finite_cost {ι : Type*} (J : Finset ι) (d : ι → ℝ) (t : ι → ℕ)
    (N : ℕ) (hN : ∀ j∈J, t j≤N) :
    let K := fun n => ∑ j ∈ J,d j*cutoffStep (t j) n
    Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n)) ≤
      ∑ j ∈ J,|d j| * Real.sqrt |M (t j)| := by
  let F := fun j => d j • cutoffStep (t j)
  have hF : (fun n => ∑ j ∈ J,d j*cutoffStep (t j) n) = ∑ j ∈ J,F j := by
    ext n
    simp [F,Finset.sum_apply]
  rw [hF]
  dsimp only
  rw [← norm_rank_residual N (∑ j ∈ J,F j),map_sum]
  apply (norm_sum_le J _).trans
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [show F j=d j • cutoffStep (t j) from rfl,map_smul,norm_smul,
    Real.norm_eq_abs,norm_rank_residual]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (rank_step_cost_le_mertens N (t j) (hN j hj)))
    (abs_nonneg _)

theorem arithmetic_fourier_kernel_rank_cost {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ)
    (X Q : ℕ) (hQ : 0<Q) (hu : ∀ j∈J, Q≤u j) :
    let N := X/Q
    let K := blockKernel J u d X
    let G := averageCorrection N K
    dot N muR G=0 ∧
      Real.sqrt (sqNorm N (fun n => K n-G n)) ≤
        ∑ j ∈ J,|d j| * Real.sqrt |M (X/u j)| := by
  let N := X/Q
  let K := blockKernel J u d X
  have he : K = fun n => ∑ j ∈ J,d j*cutoffStep (X/u j) n := by
    ext n
    simp [K,blockKernel,cutoffStep,mul_ite]
  refine ⟨rank_average_mobius_orthogonal N K,?_⟩
  change Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n)) ≤ _
  rw [he]
  exact rank_aggregate_finite_cost J d (fun j => X/u j) N
    (fun j hj => Nat.div_le_div_left (hu j hj) hQ)

theorem mixed_rank_coefficients (N : ℕ) (hN : 0<N) (K : ℕ → ℝ) (n : ℕ)
    (hn : n∈Finset.Ioc 0 N) :
    averageCorrection N K n =
      ∑ t ∈ Finset.Ioc 1 N,MixedRadix.coefficients N (averageCorrection N K) t*MixedRadix.column t n :=
  MixedRadix.mixed_coefficients_reconstruct N hN _ (rank_average_mobius_orthogonal N K) n hn

end RHConnections.RankPairing
