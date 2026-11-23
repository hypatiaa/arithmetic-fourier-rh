import Verified

open Finset Filter
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

private theorem shell_primes_eq_half_shell {X : ℕ} (hX : 4 ≤ X) :
    shellPrimes X = primeHalfShell (X:ℝ) := by
  ext p
  rw [shellPrimes,mem_filter,upper_odd_shell_iff,prime_half_shell_mem (by positivity)]
  constructor
  · rintro ⟨⟨hp,hpX,hodd,hlo⟩,hprime⟩
    have h : (X:ℝ) < 2*(p:ℝ) := by exact_mod_cast hlo
    exact ⟨hprime,by linarith,by exact_mod_cast hpX⟩
  · rintro ⟨hprime,hlo,hhi⟩
    have hhi' : p ≤ X := by exact_mod_cast hhi
    have hlo' : X < 2*p := by
      exact_mod_cast (show (X:ℝ) < 2*(p:ℝ) by linarith)
    exact ⟨⟨hprime.pos,hhi',hprime.odd_of_ne_two (by omega),hlo'⟩,hprime⟩

private theorem cofactor_partners_card {X r : ℕ} (hr : r ∈ primeCofactors) (hX : 2*43*43 ≤ X) :
    (cofactorPartners X r).card = (primeHalfShell ((X:ℝ)/r)).card := by
  obtain ⟨hrp,_,hr43,_⟩ := prime_cofactor_properties hr
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hrp.pos
  have hX0 : 0 ≤ (X:ℝ)/r := by positivity
  have hR : (r:ℝ) ≤ 43 := by exact_mod_cast hr43
  have hX' : (2*43*43:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have h43 : (43:ℝ) ≤ ((X:ℝ)/r)/2 := by
    rw [_root_.div_div,le_div_iff₀ (by positivity : 0 < (r:ℝ)*2)]
    nlinarith
  unfold cofactorPartners
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hrp.pos h),filter_eq_self.mpr]
  intro q hq
  exact_mod_cast (h43.trans_lt ((prime_half_shell_mem hX0).mp hq).2.1)

theorem semiprime_partners_card_asymptotic :
    Tendsto (fun X : ℕ => ((semiprimePartners X).card:ℝ)*Real.log (X:ℝ)/(X:ℝ))
      atTop (nhds (∑ r ∈ primeCofactors, (1:ℝ)/(2*(r:ℝ)))) := by
  have hterm (r : ℕ) (hr : r ∈ primeCofactors) :
      Tendsto (fun X : ℕ => ((primeHalfShell ((X:ℝ)/r)).card:ℝ)*Real.log (X:ℝ)/(X:ℝ))
        atTop (nhds ((1:ℝ)/(2*(r:ℝ)))) :=
    (prime_half_shell_scaled_ratio (r := (r:ℝ))
      (Nat.cast_pos.mpr (prime_cofactor_properties hr).1.pos)).comp tendsto_natCast_atTop_atTop
  have h := tendsto_finsetSum primeCofactors hterm
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2*43*43:ℕ)] with X hX
  have hCard := Finset.card_biUnion (cofactor_partner_pairwise_disjoint X)
  change (∑ r ∈ primeCofactors, ((primeHalfShell ((X:ℝ)/r)).card:ℝ)*Real.log (X:ℝ)/(X:ℝ)) =
    ((semiprimePartners X).card:ℝ)*Real.log (X:ℝ)/(X:ℝ)
  rw [semiprimePartners,hCard,Nat.cast_sum,Finset.sum_mul,Finset.sum_div]
  exact Finset.sum_congr rfl (fun r hr => by rw [cofactor_partners_card hr hX])

theorem shell_primes_card_asymptotic :
    Tendsto (fun X : ℕ => ((shellPrimes X).card:ℝ)*Real.log (X:ℝ)/(X:ℝ)) atTop (nhds (1/2)) := by
  refine (prime_half_shell_ratio.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (4:ℕ)] with X hX
  simp only [Function.comp_apply,shell_primes_eq_half_shell hX]

theorem eventual_semiprime_supply :
    ∀ᶠ X : ℕ in atTop, (shellPrimes X).card ≤ (semiprimePartners X).card := by
  let L := ∑ r ∈ primeCofactors, (1:ℝ)/(2*(r:ℝ))
  have hL : 1/2 < L := by
    dsimp only [L]
    have he (r : ℕ) : (1:ℝ)/(2*(r:ℝ)) = ((1:ℝ)/(r:ℝ))/2 := by
      rw [_root_.div_div,mul_comm (r:ℝ)]
    simp_rw [he]
    rw [← Finset.sum_div]
    linarith [prime_cofactor_reciprocals_gt_one]
  have hh := (tendsto_order.mp (semiprime_partners_card_asymptotic.sub shell_primes_card_asymptotic)).1
    0 (show 0 < L-1/2 by linarith)
  filter_upwards [hh,eventually_ge_atTop (2:ℕ)] with X hX h2
  change 0 < ((semiprimePartners X).card:ℝ)*Real.log (X:ℝ)/(X:ℝ) -
    ((shellPrimes X).card:ℝ)*Real.log (X:ℝ)/(X:ℝ) at hX
  by_contra hn
  have hlog : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hc : ((semiprimePartners X).card:ℝ) ≤ (shellPrimes X).card := by
    exact_mod_cast (lt_of_not_ge hn).le
  have hu := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hlog) (Nat.cast_nonneg X)
  linarith

theorem eventual_prime_matching_preserving_paired :
    ∀ᶠ X : ℕ in atTop, ∃ B : Finset ℕ,
      B ⊆ semiprimePartners X ∧ Nonempty (↥(shellPrimes X) ≃ ↥B) ∧
      let P := shellPrimes X ∪ B
      let A := pairedBlock X ∪ P
      Disjoint (pairedBlock X) P ∧ A ⊆ upperOddShell X ∧
      (∑ n ∈ A, muR n) = 0 ∧
      (∑ n ∈ upperOddShell X \ A, muR n) = M X := by
  filter_upwards [eventual_semiprime_supply,eventually_ge_atTop (22:ℕ)] with X hX h22
  obtain ⟨B,hB,hCard⟩ := Finset.exists_subset_card_eq hX
  have hEq : Nonempty (↥(shellPrimes X) ≃ ↥B) := by
    refine ⟨Fintype.equivOfCardEq ?_⟩
    simp [hCard]
  have hP : Disjoint (shellPrimes X) B :=
    (semiprime_partners_disjoint_primes X).symm.mono_right hB
  have hA : Disjoint (pairedBlock X) (shellPrimes X ∪ B) :=
    Finset.disjoint_union_right.mpr ⟨(shell_primes_disjoint_paired h22).symm,
      (semiprime_partners_disjoint_paired X).symm.mono_right hB⟩
  have hIncl : pairedBlock X ∪ (shellPrimes X ∪ B) ⊆ upperOddShell X :=
    Finset.union_subset (paired_block_in_shell X) (Finset.union_subset (filter_subset _ _)
      (hB.trans (semiprime_partners_in_shell X)))
  have hS : (∑ n ∈ pairedBlock X ∪ (shellPrimes X ∪ B), muR n) = 0 := by
    rw [sum_union hA,paired_block_balanced,zero_add,sum_union hP,
      sum_congr rfl (fun _ hn => shell_prime_sign hn),
      sum_congr rfl (fun _ hn => semiprime_partner_sign (hB hn))]
    simp [hCard]
  exact ⟨B,hB,hEq,hA,hIncl,hS,balanced_complement_sum_eq_M hIncl hS⟩

end RHConnections.ArithmeticFourierShell
