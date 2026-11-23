import Verified

noncomputable section
namespace RHConnections.RankPairing

private theorem interval_multiples_card (s t q : ℕ) (hst : s ≤ t) (hq : 0 < q) :
    (((Finset.Ioc s t).filter fun n => q ∣ n).card : ℝ) ≤
      ((t - s : ℕ) : ℝ) / (q : ℝ) + 1 := by
  have hcard : ((Finset.Ioc s t).filter fun n => q ∣ n).card ≤
      (Finset.Ioc (s / q) (t / q)).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n / q)
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
      rw [Finset.mem_coe, Finset.mem_Ioc]
      exact ⟨(Nat.div_lt_iff_lt_mul hq).2 (by simpa [Nat.div_mul_cancel hn.2] using hn.1.1),
        Nat.div_le_div_right hn.1.2⟩
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      change a / q = b / q at hab
      rw [← Nat.div_mul_cancel ha', ← Nat.div_mul_cancel hb', hab]
  rw [Nat.card_Ioc] at hcard
  have hmono : s / q ≤ t / q := Nat.div_le_div_right hst
  have hcast : (((Finset.Ioc s t).filter fun n => q ∣ n).card : ℝ) ≤
      (t / q : ℕ) - (s / q : ℕ) := by
    exact_mod_cast (show (((Finset.Ioc s t).filter fun n => q ∣ n).card : ℝ) ≤
        ((t / q - s / q : ℕ) : ℝ) by exact_mod_cast hcard)
  have hsumS := Nat.mod_add_div s q
  have hsumT := Nat.mod_add_div t q
  have hmodS := Nat.mod_lt s hq
  have hS : (↑(s % q) : ℝ) + (q : ℝ) * (s / q : ℕ) = s := by exact_mod_cast hsumS
  have hT : (↑(t % q) : ℝ) + (q : ℝ) * (t / q : ℕ) = t := by exact_mod_cast hsumT
  have hmS : (↑(s % q) : ℝ) < q := by exact_mod_cast hmodS
  have hmT : (0 : ℝ) ≤ (t % q : ℕ) := by positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply hcast.trans
  rw [Nat.cast_sub hst, show ((t : ℝ) - s) / q + 1 = ((t : ℝ) - s + q) / q by
    field_simp]
  apply (le_div_iff₀ hq').2
  nlinarith only [hS, hT, hmS, hmT]

private theorem inverse_square_tail (k : ℕ) :
    (∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 3)^2) ≤
      1/2 - 1 / ((k : ℝ) + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ]
      have hden : 0 < (k : ℝ) + 2 := by positivity
      have hden' : 0 < (k : ℝ) + 3 := by positivity
      have hcompare : 1 / ((k : ℝ) + 3)^2 ≤
          1 / ((k : ℝ) + 2) / ((k : ℝ) + 3) := by
        rw [div_div]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have htelescope : 1 / ((k : ℝ) + 2) / ((k : ℝ) + 3) =
          1 / ((k : ℝ) + 2) - 1 / ((k : ℝ) + 3) := by
        field_simp
        ring
      rw [htelescope] at hcompare
      rw [show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring]
      linarith

private theorem inverse_square_sum (k : ℕ) :
    (∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 2)^2) ≤ 3/4 := by
  cases k with
  | zero => norm_num
  | succ k =>
      rw [Finset.sum_range_succ']
      have htail := inverse_square_tail k
      have hpos : 0 ≤ 1 / ((k : ℝ) + 2) := by positivity
      simp only [Nat.cast_succ, Nat.cast_zero, zero_add]
      have heq : ∀ i : ℕ, (i : ℝ) + 1 + 2 = (i : ℝ) + 3 := by intro i; ring
      simp_rw [heq]
      rw [show (1 : ℝ) / 2^2 = 1/4 by norm_num]
      linarith

theorem squarefree_interval_card_lower (s t : ℕ) (hst : s ≤ t) :
    (((Finset.Ioc s t).filter Squarefree).card : ℝ) ≥
      ((t - s : ℕ) : ℝ) / 4 - (t.sqrt : ℝ) := by
  classical
  let bad := (Finset.Ioc s t).filter fun n => ¬ Squarefree n
  let mult := fun i : ℕ => (Finset.Ioc s t).filter fun n => (i + 2)^2 ∣ n
  let k := t.sqrt - 1
  have hbad : bad ⊆ (Finset.range k).biUnion mult := by
    intro n hn
    change n ∈ (Finset.Ioc s t).filter (fun n => ¬ Squarefree n) at hn
    obtain ⟨hn, hnonsq⟩ := Finset.mem_filter.mp hn
    have hn' := Finset.mem_Ioc.mp hn
    rw [Squarefree, not_forall] at hnonsq
    obtain ⟨d, hd⟩ := hnonsq
    rw [not_imp] at hd
    have hnpos : 0 < n := by omega
    have hdsq := Nat.le_of_dvd hnpos hd.1
    have hdpos : 0 < d := by
      by_contra! hd0
      have heq : d = 0 := by omega
      simp [heq, hnpos.ne'] at hd
    have hdne : d ≠ 1 := by intro heq; exact hd.2 (heq ▸ isUnit_one)
    have hdroot : d ≤ t.sqrt := Nat.le_sqrt.mpr (hdsq.trans hn'.2)
    have hdeq : d - 2 + 2 = d := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨d - 2, Finset.mem_range.mpr ?_, Finset.mem_filter.mpr ⟨hn, ?_⟩⟩
    · dsimp [k]; omega
    · rw [hdeq, pow_two]; exact hd.1
  have hbound : (bad.card : ℝ) ≤
      ∑ i ∈ Finset.range k, (((t - s : ℕ) : ℝ) *
        (1 / ((i : ℝ) + 2)^2) + 1) := by
    have hnat : bad.card ≤ ∑ i ∈ Finset.range k, (mult i).card :=
      (Finset.card_le_card hbad).trans Finset.card_biUnion_le
    calc
      (bad.card : ℝ) ≤ ∑ i ∈ Finset.range k, ((mult i).card : ℝ) := by exact_mod_cast hnat
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have h := interval_multiples_card s t ((i + 2)^2) hst (by positivity)
        simpa [mult, Nat.cast_pow, Nat.cast_add, div_eq_mul_inv, mul_assoc] using h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hbound
  have hk : (k : ℝ) ≤ t.sqrt := by exact_mod_cast Nat.sub_le t.sqrt 1
  have hmain := mul_le_mul_of_nonneg_left (inverse_square_sum k)
    (Nat.cast_nonneg (α := ℝ) (t - s))
  have hsplit : ((Finset.Ioc s t).filter Squarefree).card + bad.card = t - s := by
    rw [← Nat.card_Ioc]
    dsimp [bad]
    exact Finset.card_filter_add_card_filter_not Squarefree
  have hsplit' : (((Finset.Ioc s t).filter Squarefree).card : ℝ) + bad.card =
      ((t - s : ℕ) : ℝ) := by exact_mod_cast hsplit
  linarith

end RHConnections.RankPairing
