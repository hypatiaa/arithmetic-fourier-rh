import Verified
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace RHConnections.SpectralTail

def heightBin (t : ℝ) : ℕ := by
  classical
  exact Nat.find (show ∃ j : ℕ, |t| < (2 : ℝ)^(j+1) by
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    exact ⟨n, hn.trans (by exact_mod_cast (n.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ n))))⟩)

theorem heightBin_upper (t : ℝ) : |t| < (2 : ℝ)^(heightBin t+1) := by
  unfold heightBin
  exact @Nat.find_spec (fun j => |t| < (2 : ℝ)^(j+1)) _ _

theorem heightBin_lower (t : ℝ) (h : heightBin t ≠ 0) : (2 : ℝ)^heightBin t ≤ |t| := by
  classical
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
  have hlt : k < heightBin t := by omega
  have hh : ¬ |t| < (2 : ℝ)^(k+1) := Nat.find_min _ hlt
  exact hk ▸ le_of_not_gt hh

theorem heightBin_decay (t : ℝ) :
    1 / (1+t^2) ≤ ((1/2 : ℝ)^heightBin t)^2 := by
  by_cases h : heightBin t = 0
  · simp only [h, pow_zero, one_pow]
    exact (div_le_iff₀ (by positivity)).2 (by nlinarith [sq_nonneg t])
  have hl := heightBin_lower t h
  have hs : ((2 : ℝ)^heightBin t)^2 ≤ t^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ)^heightBin t) hl 2
    simpa [sq_abs] using hh
  rw [one_div, one_div, inv_pow (2 : ℝ), inv_pow ((2 : ℝ)^heightBin t)]
  exact inv_anti₀ (by positivity) (by linarith)

theorem multiplicity_majorant_summable {ι : Type*} (ordinate : ι → ℝ)
    (mult : ι → ℕ) (C : ℝ)
    (count : ∀ (j : ℕ) (s : Finset ι), (∀ i ∈ s, |ordinate i| < (2 : ℝ)^(j+1)) →
      (∑ i ∈ s, (mult i : ℝ)) ≤ C * ((j : ℝ)+1) * 2^j) :
    Summable (fun i => (mult i : ℝ)/(1+(ordinate i)^2)) := by
  let f (i : ι) := (mult i : ℝ)/(1+(ordinate i)^2)
  let S (j : ℕ) := {i : ι | heightBin (ordinate i) = j}
  have hf : 0 ≤ f := fun i => by dsimp [f]; positivity
  have hpart (i : ι) : ∃! j, i ∈ S j :=
    ⟨heightBin (ordinate i), rfl, fun _ h => (show heightBin (ordinate i) = _ from h).symm⟩
  have hsum (j : ℕ) (s : Finset (S j)) :
      (∑ i ∈ s, f i) ≤ C * dyadicWeight j := by
    let e : S j ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
    let b : ℝ := ((1/2 : ℝ)^j)^2
    have hm := count j (s.map e) (by
      intro i hi
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
      change |ordinate k| < (2 : ℝ)^(j+1)
      have hk : heightBin (ordinate k) = j := k.property
      simpa only [hk] using heightBin_upper (ordinate k))
    simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk] at hm
    calc
      _ ≤ ∑ i ∈ s, (mult i : ℝ)*b := by
        apply Finset.sum_le_sum
        intro i _
        have heq : f i = (mult i : ℝ)*(1/(1+(ordinate i)^2)) := by simp [f, div_eq_mul_inv]
        have hj : heightBin (ordinate i) = j := i.property
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by simpa only [b, hj] using heightBin_decay (ordinate i)) (Nat.cast_nonneg _)
      _ = (∑ i ∈ s, (mult i : ℝ))*b := (Finset.sum_mul ..).symm
      _ ≤ (C*((j : ℝ)+1)*2^j)*b := mul_le_mul_of_nonneg_right hm (sq_nonneg _)
      _ = _ := by
        have hprod : (2 : ℝ)^j * (1/2 : ℝ)^j = 1 := by rw [← mul_pow]; norm_num
        dsimp [b, dyadicWeight]
        rw [pow_two]
        calc
          _ = C * (((j : ℝ)+1) * ((2:ℝ)^j * (1/2:ℝ)^j) * (1/2:ℝ)^j) := by ring
          _ = _ := by rw [hprod, mul_one]
  have hinner (j : ℕ) : Summable (fun i : S j => f i) :=
    summable_of_sum_le (fun i => hf i) (hsum j)
  apply (summable_partition hf hpart).2
  refine ⟨hinner, (dyadic_summable.mul_left C).of_nonneg_of_le
    (fun j => tsum_nonneg (fun i => hf i)) (fun j => ?_)⟩
  exact le_of_tendsto (hinner j).hasSum (Filter.Eventually.of_forall (hsum j))

end RHConnections.SpectralTail
