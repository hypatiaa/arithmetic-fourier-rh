import Verified

namespace RHConnections.CrossingPairing

def crossings (P N p n : ℕ) : Finset ℕ :=
  Finset.Ico (min p n) (min (max p n) (min P N))

def unmatchedInside (P N p n : ℕ) : ℕ :=
  (Finset.Ico (min P N) p).card + (Finset.Ico (min P N) n).card

theorem mem_crossings {P N p n i : ℕ} :
    i ∈ crossings P N p n ↔ i < min P N ∧ ((i < p ∧ n ≤ i) ∨ (i < n ∧ p ≤ i)) := by
  simp only [crossings, Finset.mem_Ico]
  omega

theorem cutoff_count {P N p n : ℕ} (hp : p ≤ P) (hn : n ≤ N) :
    (crossings P N p n).card + unmatchedInside P N p n =
      max p n - min p n := by
  simp only [crossings, unmatchedInside, Nat.card_Ico]
  omega

theorem cutoff_count_abs {P N p n : ℕ} (hp : p ≤ P) (hn : n ≤ N) :
    (((crossings P N p n).card + unmatchedInside P N p n : ℕ) : ℤ) =
      |(p : ℤ) - n| := by
  rw [cutoff_count hp hn, Nat.cast_sub (by omega : min p n ≤ max p n)]
  by_cases h : p ≤ n
  · simp [max_eq_right h, min_eq_left h, abs_of_nonpos (by omega : (p : ℤ) - n ≤ 0)]
  · have h' : n ≤ p := by omega
    simp [max_eq_left h', min_eq_right h', abs_of_nonneg (by omega : 0 ≤ (p : ℤ) - n)]

theorem pair_residual_sq (a b : ℝ) :
    (a - (a+b)/2)^2 + (b - (a+b)/2)^2 = (a-b)^2/2 := by ring

theorem pair_step_residual_sq (i p n : ℕ) :
    ((if i < p then (1 : ℝ) else 0) - (if i < n then 1 else 0))^2 / 2 =
    (if (i < p ∧ n ≤ i) ∨ (i < n ∧ p ≤ i) then 1/2 else 0) := by
  by_cases hp : i < p <;> by_cases hn : i < n <;> simp [hp, hn, Nat.le_of_not_gt,
    Nat.not_le_of_lt]

noncomputable def cutoffEnergy (P N p n : ℕ) : ℝ :=
  ((crossings P N p n).card : ℝ)/2 + unmatchedInside P N p n

theorem cutoff_energy_le {P N p n : ℕ} (hp : p ≤ P) (hn : n ≤ N) :
    cutoffEnergy P N p n ≤ |(p : ℝ) - n| := by
  have hc : ((crossings P N p n).card : ℝ) + unmatchedInside P N p n =
      |(p : ℝ) - n| := by exact_mod_cast cutoff_count_abs hp hn
  unfold cutoffEnergy
  rw [← hc]
  have h0 : (0 : ℝ) ≤ (crossings P N p n).card := by positivity
  linarith

def stepValue (i p : ℕ) : ℝ := if i < p then 1 else 0

theorem ordered_step_product {i p n q m : ℕ} (hp : p ≤ q) (hn : n ≤ m) :
    (stepValue i p - stepValue i n) * (stepValue i q - stepValue i m) =
    (if ((i < p ∧ n ≤ i) ∨ (i < n ∧ p ≤ i)) ∧
        ((i < q ∧ m ≤ i) ∨ (i < m ∧ q ≤ i)) then 1 else 0) := by
  unfold stepValue
  split_ifs <;> norm_num <;> omega

private theorem sum_indicator {s t : Finset ℕ} (h : t ⊆ s) :
    (∑ i ∈ s, (if i ∈ t then (1 : ℝ) else 0)) = t.card := by
  rw [← Finset.sum_filter]
  suffices he : s.filter (· ∈ t) = t by simp [he]
  ext i
  simp [and_iff_right_of_imp (fun hi => h hi : i ∈ t → i ∈ s)]

theorem paired_step_gram {P N p n q m : ℕ} (hp : p ≤ q) (hn : n ≤ m) :
    (∑ i ∈ Finset.range (min P N),
      (stepValue i p - stepValue i n) * (stepValue i q - stepValue i m)) =
    ((crossings P N p n ∩ crossings P N q m).card : ℝ) := by
  rw [← sum_indicator (s := Finset.range (min P N))
    (t := crossings P N p n ∩ crossings P N q m) (by
      intro i hi
      exact Finset.mem_range.mpr (mem_crossings.mp (Finset.mem_inter.mp hi).1).1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [ordered_step_product hp hn, mem_crossings, Finset.mem_range.mp hi]

theorem unmatched_step_gram {k a b T : ℕ} (hab : a ≤ b) (haT : a ≤ T) :
    (∑ i ∈ Finset.Ico k T, stepValue i a * stepValue i b) =
      ((Finset.Ico k a).card : ℝ) := by
  rw [← sum_indicator (s := Finset.Ico k T) (t := Finset.Ico k a) (by
    intro i hi
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi).1, lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 haT⟩)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [stepValue, Finset.mem_Ico, (Finset.mem_Ico.mp hi).1, true_and]
  split_ifs <;> norm_num
  omega

theorem cutoff_gram {P N p n q m : ℕ} (hp : p ≤ q) (hn : n ≤ m)
    (hq : q ≤ P) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (min P N),
      (stepValue i p - stepValue i n) * (stepValue i q - stepValue i m)) / 2 +
    (∑ i ∈ Finset.Ico (min P N) P, stepValue i p * stepValue i q) +
    (∑ i ∈ Finset.Ico (min P N) N, stepValue i n * stepValue i m) =
    ((crossings P N p n ∩ crossings P N q m).card : ℝ)/2 + unmatchedInside P N p n := by
  rw [paired_step_gram hp hn, unmatched_step_gram hp (hp.trans hq),
    unmatched_step_gram hn (hn.trans hm)]
  simp [unmatchedInside, add_assoc]

theorem separated_crossings {P N p n q m : ℕ} (h : max p n ≤ min q m) :
    crossings P N p n ∩ crossings P N q m = ∅ := by
  ext i
  simp only [Finset.mem_inter, mem_crossings, Finset.notMem_empty, iff_false]
  omega

theorem unmatchedInside_zero {P N p n : ℕ} (h : max p n ≤ min P N) :
    unmatchedInside P N p n = 0 := by
  simp only [unmatchedInside, Nat.card_Ico]
  omega

theorem cutoff_gram_zero {P N p n q m : ℕ} (hp : p ≤ q) (hn : n ≤ m)
    (hq : q ≤ P) (hm : m ≤ N) (hgap : max p n ≤ min q m)
    (htail : max p n ≤ min P N) :
    (∑ i ∈ Finset.range (min P N),
      (stepValue i p - stepValue i n) * (stepValue i q - stepValue i m)) / 2 +
    (∑ i ∈ Finset.Ico (min P N) P, stepValue i p * stepValue i q) +
    (∑ i ∈ Finset.Ico (min P N) N, stepValue i n * stepValue i m) = 0 := by
  rw [cutoff_gram hp hn hq hm, separated_crossings hgap, unmatchedInside_zero htail]
  simp

theorem separation_iff_activity {p n q m : ℕ} :
    max p n ≤ min q m ↔
    |(p : ℤ) - n| + |(q : ℤ) - m| ≤ (q : ℤ) + m - p - n := by
  simp only [abs_eq_max_neg]
  omega

end RHConnections.CrossingPairing
