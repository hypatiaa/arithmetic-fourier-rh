import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks
open ArithmeticFourierInversion

private theorem sqrt_nat_le_real (Q : ℕ) : (Q.sqrt:ℝ) ≤ Real.sqrt (Q:ℝ) := by
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast Nat.sqrt_le' Q)

private theorem logarithm_le_four_sqrt (Q : ℕ) (hQ : 0<Q) :
    Real.log (2+2*(Q:ℝ)) ≤ 4*Real.sqrt (Q:ℝ) := by
  have h1 : (1:ℝ) ≤ Q := by exact_mod_cast Nat.one_le_of_lt hQ
  have h := Real.log_le_rpow_div (by positivity : (0:ℝ)≤2+2*(Q:ℝ))
    (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at h
  have hs := Real.sqrt_le_sqrt (show 2+2*(Q:ℝ) ≤ 4*(Q:ℝ) by linarith only [h1])
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at hs
  linarith only [h,hs]

theorem good_block_scalar_mass (B Q : ℕ) (hQ : 0<Q)
    (hgood : |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1) :
    |∑ q ∈ Finset.Ioc Q (Q+Q.sqrt),(shortWeight B q-1)| ≤ 4*Real.log (2+2*(Q:ℝ))+1 := by
  rw [short_weight_mass]
  obtain ⟨ha,hb⟩ := block_prime_correction B Q Q.sqrt hQ
  have hqr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hroot : (Q.sqrt:ℝ) ≤ Q := by exact_mod_cast Nat.sqrt_le_self Q
  have hcard : (Q:ℝ)+(Q.sqrt:ℝ) ≤ 2+2*(Q:ℝ) := by linarith only [hroot]
  have hlog := Real.log_le_log (show (0:ℝ)<(Q:ℝ)+(Q.sqrt:ℝ) by positivity) hcard
  have hlo : 0 ≤ Real.log (2+2*(Q:ℝ)) := Real.log_nonneg (by linarith only [hqr])
  have hc : (Q.sqrt:ℝ)*Real.log ((Q:ℝ)+(Q.sqrt:ℝ))/(Q:ℝ) ≤ Real.log (2+2*(Q:ℝ)) := by
    apply (div_le_iff₀ hqr).mpr
    exact mul_le_mul hroot hlog (by
      apply Real.log_nonneg
      exact_mod_cast ((Nat.one_le_of_lt hQ).trans (Nat.le_add_right Q Q.sqrt))) hqr.le
      |>.trans_eq (mul_comm _ _)
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg ha]; linarith only [hb,hc,hgood])

private theorem scalar_size (B n : ℕ) : |S B n| ≤ (n:ℝ) := by
  have hz : S B 0 = 0 := by simp [S]
  simpa [hz] using scalar_S_lipschitz B 0 n (Nat.zero_le _)

theorem good_block_scalar_comparison (B X Q : ℕ) (hQ : 0<Q)
    (hgood : |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1) :
    let I := Finset.Ioc Q (Q+Q.sqrt)
    let term := fun q => (shortWeight B q-1)*S B (X/q)
    |∑ q ∈ I,term q| ≤
      (4*Real.log (2+2*(Q:ℝ))+1)*|S B (X/Q)| +
        19*(Real.sqrt (Q:ℝ)+(X:ℝ)/(Q:ℝ)) ∧
    (∑ q ∈ I, |term q|) ≤ 19*Real.sqrt (Q:ℝ)*((X/Q:ℕ):ℝ) := by
  let m := ∑ q ∈ Finset.Ioc Q (Q+Q.sqrt),(shortWeight B q-1)
  have hm := good_block_scalar_mass B Q hQ hgood
  change |m| ≤ _ at hm
  have hs := sqrt_nat_le_real Q
  have hqr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hs1 : (1:ℝ) ≤ Real.sqrt (Q:ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_of_lt hQ)
  have hp : 2*(Q.sqrt:ℝ)+|m| ≤ 19*Real.sqrt (Q:ℝ) := by
    linarith only [hm,hs,hs1,logarithm_le_four_sqrt Q hQ]
  have hD : 0 ≤ 1+(X:ℝ)*(Q.sqrt:ℝ)/(Q:ℝ)^2 := by positivity
  have hrest : (19*Real.sqrt (Q:ℝ))*(1+(X:ℝ)*(Q.sqrt:ℝ)/(Q:ℝ)^2) ≤
      19*(Real.sqrt (Q:ℝ)+(X:ℝ)/(Q:ℝ)) := by
    calc
      _ ≤ (19*Real.sqrt (Q:ℝ))*(1+(X:ℝ)*Real.sqrt (Q:ℝ)/(Q:ℝ)^2) := by
        gcongr
      _ = _ := by
        field_simp
        ring_nf
        rw [Real.sq_sqrt hqr.le]
  constructor
  · have h := scalar_short_block_bound B X Q Q.sqrt hQ
    dsimp only at h ⊢
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hm (abs_nonneg _))
      ((mul_le_mul_of_nonneg_right hp hD).trans hrest))
  · have h := block_termwise_bound (S B) (shortWeight B) X Q Q.sqrt hQ
      (fun q _ => short_weight_nonneg B q) (scalar_size B)
    exact h.trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))

theorem fourth_power_block_comparison (B Q : ℕ) (hQ : 0<Q)
    (hgood : |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1) :
    let I := Finset.Ioc Q (Q+Q.sqrt)
    let term := fun q => (shortWeight B q-1)*S B (Q^4/q)
    |∑ q ∈ I,term q| ≤
      (4*Real.log (2+2*(Q:ℝ))+20)*(Q:ℝ)^3+19*Real.sqrt (Q:ℝ) ∧
    (∑ q ∈ I, |term q|) ≤ 19*Real.sqrt (Q:ℝ)*(Q:ℝ)^3 := by
  have hdiv : Q^4/Q = Q^3 := by
    rw [show Q^4 = Q^3*Q from pow_succ Q 3]
    exact Nat.mul_div_cancel (Q^3) hQ
  have hq : (0:ℝ)<Q := by exact_mod_cast hQ
  have hd : (Q:ℝ)^4/(Q:ℝ) = (Q:ℝ)^3 := by field_simp
  have h := good_block_scalar_comparison B (Q^4) Q hQ hgood
  dsimp only at h ⊢
  rw [hdiv] at h
  simp only [Nat.cast_pow,hd] at h
  refine ⟨h.1.trans ?_,h.2⟩
  have hl : 0 ≤ 4*Real.log (2+2*(Q:ℝ))+1 := by
    have := Real.log_nonneg (show (1:ℝ)≤2+2*(Q:ℝ) by linarith only [hq])
    linarith
  have hsize := scalar_size B (Q^3)
  rw [Nat.cast_pow] at hsize
  have hmul := mul_le_mul_of_nonneg_left hsize hl
  linarith only [hmul]

theorem arbitrarily_late_fourth_power_comparisons (h : TwoSidedPsiOscillations) (B N : ℕ) :
    ∃ Q ≥ N, 0<Q ∧
      |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1 ∧
      (let I := Finset.Ioc Q (Q+Q.sqrt)
       let term := fun q => (shortWeight B q-1)*S B (Q^4/q)
       |∑ q ∈ I,term q| ≤
         (4*Real.log (2+2*(Q:ℝ))+20)*(Q:ℝ)^3+19*Real.sqrt (Q:ℝ) ∧
       (∑ q ∈ I, |term q|) ≤ 19*Real.sqrt (Q:ℝ)*(Q:ℝ)^3) := by
  obtain ⟨Q,hQ,hgood⟩ := arbitrarily_late_balanced_blocks h (max 1 N)
  have hp : 0 < Q := by omega
  exact ⟨Q,by omega,hp,hgood,fourth_power_block_comparison B Q hp hgood⟩

end RHConnections.ArithmeticFourierShortBlocks
