import Verified
import RadixMellin

noncomputable section
namespace RHConnections.RadixMellin

theorem weight_at_rational_sample (r t n N : ℕ) (ht : 0<t) (hn : 0<n) (hN : 0<N) :
    weight r (((n:ℝ)/(N:ℝ))/((t:ℝ)/(N:ℝ))) = ((t/n%r:ℕ):ℂ) := by
  have ht' : (t:ℝ)≠0 := by exact_mod_cast ht.ne'
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hN' : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hfrac : (((n:ℝ)/(N:ℝ))/((t:ℝ)/(N:ℝ)))⁻¹ = (t:ℝ)/(n:ℝ) := by
    field_simp
  rw [weight,hfrac,residue_mod,Nat.floor_div_natCast,Nat.floor_natCast]

theorem mixed_column_sample_identity (t n N : ℕ) (ht : 0<t) (hn : 0<n) (hN : 0<N) :
    let x := ((n:ℝ)/(N:ℝ))/((t:ℝ)/(N:ℝ))
    (MixedRadix.column t n:ℂ) = (weight 2 x+weight 3 x)/2+
      (if 3≤t ∧ n=1 then (3:ℂ)/2 else 0) := by
  dsimp only
  rw [weight_at_rational_sample 2 t n N ht hn hN,weight_at_rational_sample 3 t n N ht hn hN]
  unfold MixedRadix.column MixedRadix.weight
  split_ifs <;> push_cast <;> ring

theorem radix_factor_lower_on_critical_line {r : ℕ} (hr : 0<r) {s : ℂ} (hs : s.re=1/2) :
    Real.sqrt (r:ℝ)-1 ≤ ‖RadixFloor.radixFactor r s‖ := by
  have hc : (0:ℝ)<r := by exact_mod_cast hr
  have h := norm_sub_norm_le ((r:ℂ)^(1-s)) (1:ℂ)
  rw [norm_sub_rev,norm_one,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hc,
    Complex.sub_re,Complex.one_re,hs,show (1:ℝ)-1/2=1/2 by norm_num,← Real.sqrt_eq_rpow] at h
  exact h

theorem radix_factor_ne_zero_on_critical_line {r : ℕ} (hr : 1<r) {s : ℂ} (hs : s.re=1/2) :
    RadixFloor.radixFactor r s≠0 := by
  have hr' : (1:ℝ)<r := by exact_mod_cast hr
  have h := radix_factor_lower_on_critical_line (Nat.zero_lt_one.trans hr) hs
  have hpos : 1<Real.sqrt (r:ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hr'
  intro hz
  rw [hz,norm_zero] at h
  linarith only [h,hpos]

end RHConnections.RadixMellin
