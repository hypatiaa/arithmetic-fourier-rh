import Verified
import Mathlib.NumberTheory.Chebyshev

open Filter
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open SmoothedPrimeLimit

theorem theta_ratio_tendsto_one :
    Tendsto (fun X : ℝ => Chebyshev.theta X / X) atTop (nhds 1) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hInv : Tendsto (fun X : ℝ => (Real.sqrt X)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hErr : Tendsto (fun X : ℝ => (Chebyshev.psi X-Chebyshev.theta X)/X) atTop (nhds 0) := by
    apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hInv.const_mul C)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi X)) hX.le
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
      have hs : 0 < Real.sqrt X := Real.sqrt_pos_of_pos hX
      calc
        _ ≤ C*Real.sqrt X/X := div_le_div_of_nonneg_right (hC X) hX.le
        _ = _ := by
          apply (div_eq_iff hX.ne').2
          calc
            C*Real.sqrt X = (C*(Real.sqrt X)⁻¹)*(Real.sqrt X)^2 := by
              field_simp [hs.ne']
            _ = _ := by rw [Real.sq_sqrt hX.le]
  have hlim := chebyshev_prime_number_theorem.sub hErr
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards with X
  rw [← sub_div,sub_sub_cancel]

def primeHalfShell (X : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊X/2⌋₊

theorem prime_half_shell_mem {X : ℝ} (hX : 0 ≤ X) {p : ℕ} :
    p ∈ primeHalfShell X ↔ p.Prime ∧ X/2 < p ∧ (p:ℝ) ≤ X := by
  simp only [primeHalfShell,Finset.mem_sdiff,Nat.mem_primesLE]
  rw [Nat.le_floor_iff hX,Nat.le_floor_iff (by linarith : 0 ≤ X/2)]
  constructor
  · exact fun ⟨⟨hU,hP⟩,hL⟩ => ⟨hP,lt_of_not_ge (fun h => hL ⟨h,hP⟩),hU⟩
  · exact fun ⟨hP,hL,hU⟩ => ⟨⟨hU,hP⟩,fun h => (not_le_of_gt hL) h.1⟩

private theorem log_scaled_ratio {r : ℝ} (hr : 0 < r) :
    Tendsto (fun X : ℝ => Real.log X / Real.log (X/r)) atTop (nhds 1) := by
  have hsc : Tendsto (fun X : ℝ => X/r) atTop atTop := by
    refine tendsto_atTop.mpr fun a => ?_
    filter_upwards [eventually_ge_atTop (a*r)] with X hX
    exact (le_div_iff₀ hr).mpr hX
  have hLog : Tendsto (fun X : ℝ => Real.log (X/r)) atTop atTop := Real.tendsto_log_atTop.comp hsc
  have hi := tendsto_inv_atTop_zero.comp hLog
  have hh := (hi.const_mul (Real.log r)).const_add 1
  simp only [mul_zero,add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop r] with X hX
  have hpos : 0 < X := hr.trans hX
  have hl : 0 < Real.log (X/r) := Real.log_pos ((lt_div_iff₀ hr).mpr (by simpa using hX))
  have he := Real.log_div hpos.ne' hr.ne'
  change 1+Real.log r*(Real.log (X/r))⁻¹ = Real.log X/Real.log (X/r)
  field_simp [hl.ne']
  linarith

private theorem scaled_theta_half (X : ℝ) :
    Chebyshev.theta (X/2)/X = (1/2)*(Chebyshev.theta (X/2)/(X/2)) := by
  rw [div_div_eq_mul_div]
  ring

private theorem theta_halfShell_ratio :
    Tendsto (fun X : ℝ => (Chebyshev.theta X-Chebyshev.theta (X/2))/X) atTop (nhds (1/2)) := by
  have hsc : Tendsto (fun X : ℝ => X/2) atTop atTop := by
    refine tendsto_atTop.mpr fun a => ?_
    filter_upwards [eventually_ge_atTop (a*2)] with X hX
    linarith
  have h := theta_ratio_tendsto_one.sub ((theta_ratio_tendsto_one.comp hsc).const_mul (1/2))
  norm_num at h
  refine h.congr' (Eventually.of_forall fun X => ?_)
  simp only [Function.comp_apply,sub_div,scaled_theta_half]

theorem prime_half_shell_ratio :
    Tendsto (fun X : ℝ => ((primeHalfShell X).card:ℝ)*Real.log X/X) atTop (nhds (1/2)) := by
  have hsum {X : ℝ} (hX : 2 < X) :
      ∑ p ∈ primeHalfShell X, Real.log p = Chebyshev.theta X-Chebyshev.theta (X/2) := by
    have hsub : Nat.primesLE ⌊X/2⌋₊ ⊆ Nat.primesLE ⌊X⌋₊ := by
      intro p hp
      have h := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨h.1.trans (Nat.floor_mono (by linarith)),h.2⟩
    have hS : (∑ p ∈ primeHalfShell X, Real.log p) +
        (∑ p ∈ Nat.primesLE ⌊X/2⌋₊, Real.log p) =
          ∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p := Finset.sum_sdiff hsub
    rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
    linarith
  have hlo : ∀ᶠ X : ℝ in atTop, (Chebyshev.theta X-Chebyshev.theta (X/2))/X ≤
      ((primeHalfShell X).card:ℝ)*Real.log X/X := by
    filter_upwards [eventually_gt_atTop (2:ℝ)] with X hX
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ X)
    rw [← hsum hX,← nsmul_eq_mul,← Finset.sum_const]
    exact Finset.sum_le_sum (fun p hp => Real.log_le_log (by have hp' := (prime_half_shell_mem (by linarith : 0 ≤ X)).mp hp; linarith [hp'.2.1])
      ((prime_half_shell_mem (by linarith : 0 ≤ X)).mp hp).2.2)
  have hup : ∀ᶠ X : ℝ in atTop, ((primeHalfShell X).card:ℝ)*Real.log X/X ≤
      ((Chebyshev.theta X-Chebyshev.theta (X/2))/X)*(Real.log X/Real.log (X/2)) := by
    filter_upwards [eventually_gt_atTop (2:ℝ)] with X hX
    have hXpos : 0 < X := by linarith
    have hLog : 0 < Real.log (X/2) := Real.log_pos (by linarith)
    have hLo : ((primeHalfShell X).card:ℝ)*Real.log (X/2) ≤ Chebyshev.theta X-Chebyshev.theta (X/2) := by
      rw [← hsum hX,← nsmul_eq_mul,← Finset.sum_const]
      exact Finset.sum_le_sum (fun p hp => Real.log_le_log (by linarith)
        ((prime_half_shell_mem hXpos.le).mp hp).2.1.le)
    calc
      _ = (((primeHalfShell X).card:ℝ)*Real.log (X/2)/X)*(Real.log X/Real.log (X/2)) := by
        field_simp [hXpos.ne',hLog.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hLo hXpos.le)
        (div_nonneg (Real.log_nonneg (by linarith)) hLog.le)
  have hUpper := theta_halfShell_ratio.mul (log_scaled_ratio (by norm_num : (0:ℝ)<2))
  simp only [mul_one] at hUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' theta_halfShell_ratio hUpper hlo hup

theorem prime_half_shell_scaled_ratio {r : ℝ} (hr : 0 < r) :
    Tendsto (fun X : ℝ => ((primeHalfShell (X/r)).card:ℝ)*Real.log X/X)
      atTop (nhds (1/(2*r))) := by
  have hsc : Tendsto (fun X : ℝ => X/r) atTop atTop := by
    refine tendsto_atTop.mpr fun a => ?_
    filter_upwards [eventually_ge_atTop (a*r)] with X hX
    exact (le_div_iff₀ hr).mpr hX
  have h := ((prime_half_shell_ratio.comp hsc).mul (log_scaled_ratio hr)).div_const r
  simp only [mul_one,_root_.div_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop r] with X hX
  have hXpos := hr.trans hX
  have hLog : 0 < Real.log (X/r) := Real.log_pos ((lt_div_iff₀ hr).mpr (by simpa using hX))
  change (((primeHalfShell (X/r)).card:ℝ)*Real.log (X/r)/(X/r)*(Real.log X/Real.log (X/r)))/r =
    ((primeHalfShell (X/r)).card:ℝ)*Real.log X/X
  field_simp [hr.ne',hXpos.ne',hLog.ne']

end RHConnections.ArithmeticFourierShell
