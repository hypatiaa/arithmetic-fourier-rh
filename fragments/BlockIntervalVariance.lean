import Verified
import BlockWeightedVariance
import BlockIntervalEnergy

namespace RHConnections.BlockFourier

open RHConnections.RankPairing
variable {J : ℕ} [NeZero J] {ι : Type*} [Fintype ι]

theorem interval_energy_variance (a : ι → ZMod J) (length : ι → ℕ)
    (w : ι → ℝ) (f : ZMod J → ℝ) (c : ℝ)
    (hA : 0 < ∑ i, w i*(length i:ℝ)^2) :
    let v := fun i => w i*(length i:ℝ)^2
    let h := fun i => blockIntervalSum f (a i) (length i)/(length i:ℝ)
    let A := ∑ i, v i
    let m := (∑ i, v i*h i)/A
    intervalEnergy a length w (fun x => c+f x) =
      A*(c+m)^2 + ∑ i, v i*(h i-m)^2 := by
  dsimp only
  unfold intervalEnergy
  rw [←weighted_variance_split _ _ c hA]
  apply Finset.sum_congr rfl
  intro i _
  let n := length i
  change w i*(blockIntervalSum (fun x => c+f x) (a i) n)^2 =
    (w i*(n:ℝ)^2)*(c+blockIntervalSum f (a i) n/(n:ℝ))^2
  by_cases hn : n=0
  · simp [hn,blockIntervalSum]
  · have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    have hs : blockIntervalSum (fun x => c+f x) (a i) n =
        (n:ℝ)*c + blockIntervalSum f (a i) n := by
      simp [blockIntervalSum,Finset.sum_add_distrib,nsmul_eq_mul]
    rw [hs]
    field_simp [hnR]
    <;> ring

end RHConnections.BlockFourier
