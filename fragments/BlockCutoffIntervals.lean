import Verified
import BlockIntervalShift

noncomputable section
namespace RHConnections.RankPairing

def blockActiveLength (J : ℕ) (t : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((Finset.range J).filter fun j => n ≤ t j).card

def blockCutoffKernel {J : ℕ} (d : ZMod J → ℝ) (t : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, if n ≤ t j then d (j : ZMod J) else 0

theorem block_active_filter_eq_range (J : ℕ) (t : ℕ → ℕ) (ht : Antitone t) (n : ℕ) :
    ((Finset.range J).filter fun j => n ≤ t j) =
      Finset.range (blockActiveLength J t n) := by
  induction J with
  | zero => simp [blockActiveLength]
  | succ J ih =>
    by_cases hJ : n ≤ t J
    · have hall : (Finset.range (J + 1)).filter (fun j => n ≤ t j) =
          Finset.range (J + 1) := by
        apply Finset.filter_true_of_mem
        intro j hj
        exact hJ.trans (ht (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      rw [blockActiveLength, hall, Finset.card_range]
    · have heq : (Finset.range (J + 1)).filter (fun j => n ≤ t j) =
          (Finset.range J).filter (fun j => n ≤ t j) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [hJ]
      rw [blockActiveLength, heq]
      exact ih

theorem block_cutoff_kernel_eq_interval {J : ℕ} (d : ZMod J → ℝ)
    (t : ℕ → ℕ) (ht : Antitone t) (n : ℕ) :
    blockCutoffKernel d t n = blockIntervalSum d 0 (blockActiveLength J t n) := by
  rw [blockCutoffKernel, ← Finset.sum_filter, block_active_filter_eq_range J t ht n]
  simp only [blockIntervalSum, zero_add]

private theorem block_interval_zero_split {J : ℕ} (d : ZMod J → ℝ) (m k : ℕ) :
    blockIntervalSum d 0 (m + k) =
      blockIntervalSum d 0 m + blockIntervalSum d (m : ZMod J) k := by
  unfold blockIntervalSum
  rw [Finset.sum_range_add]
  simp [Nat.cast_add, add_comm]

theorem block_cutoff_kernel_sub_of_le {J : ℕ} (d : ZMod J → ℝ) (t : ℕ → ℕ)
    (ht : Antitone t) (a b : ℕ) (hab : blockActiveLength J t b ≤ blockActiveLength J t a) :
    blockCutoffKernel d t a - blockCutoffKernel d t b =
      blockIntervalSum d (blockActiveLength J t b : ZMod J)
        (blockActiveLength J t a - blockActiveLength J t b) := by
  rw [block_cutoff_kernel_eq_interval d t ht a, block_cutoff_kernel_eq_interval d t ht b]
  have hs := block_interval_zero_split d (blockActiveLength J t b)
    (blockActiveLength J t a - blockActiveLength J t b)
  rw [Nat.add_sub_of_le hab] at hs
  rw [hs]
  ring

theorem block_cutoff_kernel_abs_sub {J : ℕ} (d : ZMod J → ℝ) (t : ℕ → ℕ)
    (ht : Antitone t) (a b : ℕ) :
    |blockCutoffKernel d t a - blockCutoffKernel d t b| =
      |blockIntervalSum d ((min (blockActiveLength J t a) (blockActiveLength J t b) : ℕ) :
        ZMod J) (max (blockActiveLength J t a) (blockActiveLength J t b) -
          min (blockActiveLength J t a) (blockActiveLength J t b))| := by
  rcases le_total (blockActiveLength J t a) (blockActiveLength J t b) with hab | hba
  · rw [min_eq_left hab, max_eq_right hab, abs_sub_comm,
      block_cutoff_kernel_sub_of_le d t ht b a hab]
  · rw [min_eq_right hba, max_eq_left hba, block_cutoff_kernel_sub_of_le d t ht a b hba]

end RHConnections.RankPairing
