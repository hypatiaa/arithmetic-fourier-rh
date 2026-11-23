import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks
open ArithmeticFourierInversion

def coeff (B : ℕ) : ArithmeticFunction ℝ := g B * muR

private theorem muR_apply_cast (n : ℕ) : muR n = (moebius n:ℝ) := rfl

theorem scalar_coeff_multiplicative (B : ℕ) : (coeff B).IsMultiplicative := by
  have hg : (g B).IsMultiplicative := ⟨by simp [g_apply],fun _ => g_mul B _ _⟩
  exact hg.mul isMultiplicative_moebius.intCast

theorem scalar_coeff_prime_pow (B p k : ℕ) (hp : p.Prime) :
    coeff B (p^(k+1)) = g B (p^(k+1)) - g B (p^k) := by
  let U : Finset (ℕ × ℕ) := {(p^(k+1),1),(p^k,p)}
  have hA : U ⊆ (p^(k+1)).divisorsAntidiagonal := by
    intro x hx
    simp only [U,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl <;> exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨by simp [pow_succ],pow_ne_zero _ hp.ne_zero⟩
  have hsum : (∑ x ∈ U,g B x.1*muR x.2) =
      ∑ x ∈ (p^(k+1)).divisorsAntidiagonal,g B x.1*muR x.2 := by
    apply Finset.sum_subset hA
    intro x hx hn
    obtain ⟨hm,_⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hd : x.2 ∣ p^(k+1) := ⟨x.1,by rw [mul_comm]; exact hm.symm⟩
    obtain ⟨j,hj,hpow⟩ := (Nat.dvd_prime_pow hp).mp hd
    by_cases hj0 : j = 0
    · have h2 : x.2 = 1 := by simpa [hj0] using hpow
      have h1 : x.1 = p^(k+1) := by simpa [h2] using hm
      have he : x = (p^(k+1),1) := Prod.ext h1 h2
      exact (hn (by simp [U,he])).elim
    by_cases hj1 : j = 1
    · have h2 : x.2 = p := by simpa [hj1] using hpow
      have h1 : x.1 = p^k := by
        apply Nat.eq_of_mul_eq_mul_right hp.pos
        simpa only [h2,pow_succ] using hm
      have he : x = (p^k,p) := Prod.ext h1 h2
      exact (hn (by simp [U,he])).elim
    · rw [hpow,muR_apply_cast,moebius_apply_prime_pow hp hj0,ite_eq_right hj1,Int.cast_zero,mul_zero]
  have hne : (p^(k+1),1) ≠ (p^k,p) := fun h => hp.ne_one (congrArg Prod.snd h).symm
  rw [coeff,ArithmeticFunction.mul_apply,← hsum]
  simp [U,Finset.sum_insert,hne,muR_apply_cast,moebius_apply_prime hp,sub_eq_add_neg]

theorem scalar_coeff_abs_le_one (B n : ℕ) : |coeff B n| ≤ 1 := by
  have hg (m : ℕ) : 0 ≤ g B m ∧ g B m ≤ 1 := by
    rw [g_apply]
    split_ifs with h
    · by_cases h0 : m = 0
      · simp [h0]
      · exact ⟨by positivity, inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0)⟩
    · norm_num
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => rw [(scalar_coeff_multiplicative B).map_one,abs_one]
  | prime_pow p n hp hn =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [scalar_coeff_prime_pow B p k hp]
    exact abs_le.mpr ⟨by linarith [(hg (p^(k+1))).1,(hg (p^k)).2],
      by linarith [(hg (p^(k+1))).2,(hg (p^k)).1]⟩
  | coprime a b _ _ hab ha hb =>
    rw [(scalar_coeff_multiplicative B).map_mul_of_coprime hab,abs_mul]
    simpa only [one_mul] using mul_le_mul ha hb (abs_nonneg _) zero_le_one

theorem partial_sum_lipschitz (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (l r : ℕ) (hlr : l ≤ r) :
    |(∑ n ∈ Finset.Ioc 0 r, a n) - ∑ n ∈ Finset.Ioc 0 l, a n| ≤ (r:ℝ)-l := by
  have hsub : Finset.Ioc (0:ℕ) l ⊆ Finset.Ioc 0 r := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2.trans hlr⟩
  have he : (Finset.Ioc (0:ℕ) r) \ Finset.Ioc 0 l = Finset.Ioc l r := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_Ioc]
    omega
  have hS : (∑ n ∈ Finset.Ioc l r, a n) + (∑ n ∈ Finset.Ioc 0 l,a n) = ∑ n ∈ Finset.Ioc 0 r,a n := by
    rw [← he]
    exact Finset.sum_sdiff hsub
  rw [← (eq_sub_of_add_eq hS)]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc l r, |a n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc l r, (1:ℝ) := Finset.sum_le_sum fun n _ => ha n
    _ = _ := by simp [Nat.card_Ioc,Nat.cast_sub hlr]

theorem scalar_S_lipschitz (B l r : ℕ) (hlr : l ≤ r) :
    |S B r-S B l| ≤ (r:ℝ)-l :=
  partial_sum_lipschitz (coeff B) (scalar_coeff_abs_le_one B) l r hlr

theorem mertens_M_lipschitz (l r : ℕ) (hlr : l ≤ r) : |M r-M l| ≤ (r:ℝ)-l := by
  exact partial_sum_lipschitz muR (fun n => by
    rw [muR_apply_cast]
    exact_mod_cast (abs_moebius_le_one (n := n))) l r hlr

end RHConnections.ArithmeticFourierShortBlocks
