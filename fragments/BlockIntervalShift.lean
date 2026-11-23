import Verified

noncomputable section
namespace RHConnections.RankPairing
open scoped BigOperators

def blockIntervalSum {J : ℕ} (d : ZMod J → ℝ) (a : ZMod J) (ℓ : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ℓ, d (a + (i : ZMod J))

private theorem block_interval_one_shift {J : ℕ} (d : ZMod J → ℝ)
    (H : ℝ) (hd : ∀ x, |d x| ≤ H) (a : ZMod J) (ℓ : ℕ) :
    |blockIntervalSum d (a + 1) ℓ - blockIntervalSum d a ℓ| ≤ 2 * H := by
  have hsum : blockIntervalSum d a (ℓ + 1) = blockIntervalSum d (a + 1) ℓ + d a := by
    unfold blockIntervalSum
    rw [Finset.sum_range_succ']
    simp [Nat.cast_add, add_comm, add_left_comm]
  have hsum' : blockIntervalSum d a (ℓ + 1) =
      blockIntervalSum d a ℓ + d (a + (ℓ : ZMod J)) := by
    exact Finset.sum_range_succ _ _
  have ht : blockIntervalSum d (a + 1) ℓ - blockIntervalSum d a ℓ =
      d (a + (ℓ : ZMod J)) - d a := by linarith
  rw [ht]
  calc
    _ ≤ |d (a + (ℓ : ZMod J))| + |d a| := abs_sub _ _
    _ ≤ 2 * H := by linarith [hd (a + (ℓ : ZMod J)), hd a]

private theorem block_interval_nat_shift {J : ℕ} (d : ZMod J → ℝ)
    (H : ℝ) (hd : ∀ x, |d x| ≤ H) (a : ZMod J) (ℓ k : ℕ) :
    |blockIntervalSum d (a + (k : ZMod J)) ℓ - blockIntervalSum d a ℓ| ≤
      2 * H * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact ((abs_sub_le _ (blockIntervalSum d (a + (k : ZMod J)) ℓ) _).trans
        (by rw [Nat.cast_succ]; linarith [block_interval_one_shift d H hd (a + (k : ZMod J)) ℓ]))

private theorem block_interval_sub_nat_shift {J : ℕ} (d : ZMod J → ℝ)
    (H : ℝ) (hd : ∀ x, |d x| ≤ H) (a : ZMod J) (ℓ k : ℕ) :
    |blockIntervalSum d (a - (k : ZMod J)) ℓ - blockIntervalSum d a ℓ| ≤
      2 * H * (k : ℝ) := by
  have h := block_interval_nat_shift d H hd (a - (k : ZMod J)) ℓ k
  rw [sub_add_cancel, abs_sub_comm] at h
  exact h

theorem block_interval_int_shift {J : ℕ} (d : ZMod J → ℝ)
    (H : ℝ) (hd : ∀ x, |d x| ≤ H) (a : ZMod J) (ℓ : ℕ) (z : ℤ) :
    |blockIntervalSum d (a + (z : ZMod J)) ℓ - blockIntervalSum d a ℓ| ≤
      2 * H * |(z : ℝ)| := by
  cases z with
  | ofNat k =>
      simpa [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)] using
        block_interval_nat_shift d H hd a ℓ k
  | negSucc k =>
      have hz : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := by rw [Int.negSucc_eq, Nat.cast_succ]
      rw [hz]
      simp only [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k + 1))]
      exact block_interval_sub_nat_shift d H hd a ℓ (k + 1)

def blockCyclicDistance {J : ℕ} (h : ZMod J) : ℕ := min h.val (J - h.val)

theorem block_interval_cyclic_shift {J : ℕ} [NeZero J] (d : ZMod J → ℝ)
    (H : ℝ) (hd : ∀ x, |d x| ≤ H) (a : ZMod J) (ℓ : ℕ) (h : ZMod J) :
    |blockIntervalSum d (a + h) ℓ - blockIntervalSum d a ℓ| ≤
      2 * H * (blockCyclicDistance h : ℝ) := by
  by_cases he : h.val ≤ J - h.val
  · rw [blockCyclicDistance, min_eq_left he]
    simpa [ZMod.natCast_zmod_val] using block_interval_nat_shift d H hd a ℓ h.val
  · rw [blockCyclicDistance, min_eq_right (le_of_not_ge he)]
    have hc : ((J - h.val : ℕ) : ZMod J) = -h := by
      rw [Nat.cast_sub (ZMod.val_lt h).le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
    simpa [hc] using block_interval_sub_nat_shift d H hd a ℓ (J - h.val)

theorem block_interval_smoothing {J : ℕ} [NeZero J] (d L : ZMod J → ℝ)
    (H : ℝ) (hd : ∀ x, |d x| ≤ H) (hL : ∑ h, L h = 1)
    (a : ZMod J) (ℓ : ℕ) :
    |blockIntervalSum (fun x => d x - ∑ h, L h * d (x + h)) a ℓ| ≤
      2 * H * ∑ h, |L h| * (blockCyclicDistance h : ℝ) := by
  classical
  have hweighted : ∑ h, L h * blockIntervalSum d a ℓ = blockIntervalSum d a ℓ := by
    rw [← Finset.sum_mul, hL, one_mul]
  have heq : blockIntervalSum (fun x => d x - ∑ h, L h * d (x + h)) a ℓ =
      ∑ h, L h * (blockIntervalSum d a ℓ - blockIntervalSum d (a + h) ℓ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hweighted]
    simp only [blockIntervalSum, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.range ℓ)]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro i _
    rw [add_right_comm a]
  rw [heq, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro h _
  rw [abs_mul, abs_sub_comm, mul_left_comm (2 * H)]
  exact mul_le_mul_of_nonneg_left (block_interval_cyclic_shift d H hd a ℓ h) (abs_nonneg _)

end RHConnections.RankPairing
