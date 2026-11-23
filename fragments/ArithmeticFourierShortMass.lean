import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks
open ArithmeticFourierInversion

def blockDiscrepancy (Q H : ℕ) : ℝ :=
  (∑ q ∈ Finset.Ioc Q (Q+H), vonMangoldt q) - H

theorem short_weight_mass (B Q H : ℕ) :
    (∑ q ∈ Finset.Ioc Q (Q+H), (shortWeight B q-1)) =
      blockDiscrepancy Q H - ∑ q ∈ Finset.Ioc Q (Q+H),vonMangoldt q * g B q := by
  simp only [shortWeight,blockDiscrepancy,mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,
    nsmul_eq_mul,mul_one,Nat.card_Ioc,Nat.add_sub_cancel_left]
  ring

theorem block_prime_correction (B Q H : ℕ) (hQ : 0 < Q) :
    0 ≤ (∑ q ∈ Finset.Ioc Q (Q+H), vonMangoldt q * g B q) ∧
    (∑ q ∈ Finset.Ioc Q (Q+H), vonMangoldt q * g B q) ≤
      (H:ℝ)*Real.log ((Q:ℝ)+H)/(Q:ℝ) := by
  have hg (q : ℕ) (hq : Q ≤ q) : 0 ≤ g B q ∧ g B q ≤ (Q:ℝ)⁻¹ := by
    rw [g_apply]
    split_ifs
    · exact ⟨by positivity,inv_anti₀ (by exact_mod_cast hQ) (by exact_mod_cast hq)⟩
    · exact ⟨le_rfl,by positivity⟩
  refine ⟨Finset.sum_nonneg fun q hq => mul_nonneg vonMangoldt_nonneg (hg q (Finset.mem_Ioc.mp hq).1.le).1,?_⟩
  calc
    _ ≤ ∑ _q ∈ Finset.Ioc Q (Q+H), Real.log ((Q:ℝ)+H) * (Q:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hq
      exact mul_le_mul (vonMangoldt_le_log.trans (Real.log_le_log
        (by exact_mod_cast hQ.trans hl) (by exact_mod_cast hu)))
        (hg q hl.le).2 (hg q hl.le).1 (by
          apply Real.log_nonneg
          exact_mod_cast (Nat.one_le_of_lt hQ).trans (Nat.le_add_right Q H))
    _ = _ := by simp [Nat.card_Ioc,div_eq_mul_inv,mul_assoc]

theorem block_termwise_bound (F b : ℕ → ℝ) (X Q H : ℕ) (hQ : 0<Q)
    (hb : ∀ q ∈ Finset.Ioc Q (Q+H), 0 ≤ b q) (hF : ∀ n, |F n| ≤ (n:ℝ)) :
    let I := Finset.Ioc Q (Q+H)
    let m := ∑ q ∈ I, (b q-1)
    (∑ q ∈ I, |(b q-1)*F (X/q)|) ≤ (2*(H:ℝ)+|m|)*((X/Q:ℕ):ℝ) := by
  let I := Finset.Ioc Q (Q+H)
  let m := ∑ q ∈ I, (b q-1)
  change (∑ q ∈ I, _) ≤ (2*(H:ℝ)+|m|)*_
  have he : (∑ q ∈ I, (b q+1)) = 2*(H:ℝ)+m := by
    simp [m,I,Finset.sum_add_distrib,Finset.sum_sub_distrib,Nat.card_Ioc]
    ring
  calc
    _ ≤ ∑ q ∈ I,(b q+1)*((X/Q:ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqQ := (Finset.mem_Ioc.mp hq).1
      rw [abs_mul]
      exact mul_le_mul ((abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hb q hq),abs_one]))
        ((hF _).trans (by exact_mod_cast Nat.div_le_div_left hqQ.le hQ)) (abs_nonneg _) (by linarith only [hb q hq])
    _ ≤ _ := by
      rw [← Finset.sum_mul,he]
      exact mul_le_mul_of_nonneg_right (add_le_add (le_refl _) (le_abs_self m)) (Nat.cast_nonneg _)

end RHConnections.ArithmeticFourierShortBlocks
