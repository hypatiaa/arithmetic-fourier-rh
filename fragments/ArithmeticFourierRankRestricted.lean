import Verified
import ArithmeticFourierRankCost

open ArithmeticFunction
noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierInversion ArithmeticFourierMertensKernel ArithmeticFourierDyadic
  ArithmeticFourierShortBlocks

theorem dyadic_block_discrepancy_l1 (Q r : ℕ) (u : ℕ → ℕ) (hu : Monotone u)
    (h0 : u 0=Q) (hr : u r=2*Q) :
    (∑ j ∈ Finset.range r,|blockVM u j|) ≤ (2*(Real.log 4+4)+1)*(Q:ℝ) := by
  have hj (j : ℕ) : blockVM u j =
      (∑ z ∈ Finset.Ioc (u j) (u (j+1)),vonMangoldt z)-((u (j+1):ℝ)-(u j:ℝ)) := by
    let L := u (j+1)-u j
    have hsum : u j+L=u (j+1) := Nat.add_sub_of_le (hu (Nat.le_succ j))
    have he := block_discrepancy_eq_remainder (u j) L
    unfold blockDiscrepancy at he
    rw [hsum] at he
    have hL : (L:ℝ)=(u (j+1):ℝ)-(u j:ℝ) := Nat.cast_sub (hu (Nat.le_succ j))
    rw [hL] at he
    exact he.symm
  have hcount : (∑ z ∈ Finset.Ioc Q (2*Q),vonMangoldt z) ≤ Chebyshev.psi (2*(Q:ℝ)) := by
    rw [show (2:ℝ)*(Q:ℝ)=((2*Q:ℕ):ℝ) by norm_num,Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun n hn =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Ioc.mp hn).2⟩) (fun _ _ _ => vonMangoldt_nonneg)
  calc
    _ ≤ ∑ j ∈ Finset.range r,
      ((∑ z ∈ Finset.Ioc (u j) (u (j+1)),vonMangoldt z)+((u (j+1):ℝ)-(u j:ℝ))) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [hj]
      refine (abs_sub _ _).trans_eq ?_
      rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)),
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (hu (Nat.le_succ j))))]
    _ = (∑ z ∈ Finset.Ioc Q (2*Q),vonMangoldt z)+(Q:ℝ) := by
      rw [Finset.sum_add_distrib,partition_sum_telescope _ hu,h0,hr,
        sum_block_differences (fun j => (u j:ℝ)) r,h0,hr,Nat.cast_mul,Nat.cast_ofNat]
      ring
    _ ≤ _ := by
      have h := hcount.trans (Chebyshev.psi_le_const_mul_self (by positivity : 0≤(2:ℝ)*(Q:ℝ)))
      linarith only [h]

theorem rank_cost_restricted_power {X Q r : ℕ} (hQ : 0<Q)
    (u : ℕ → ℕ) (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q)
    (A c C : ℝ) (hA : 0<A) (hc : 0<c) (hC : 0≤C)
    (hrange : Real.log (Q:ℝ) ≤ A*Real.sqrt (Real.log ((X/Q:ℕ):ℝ)))
    (hM : ∀ j ∈ Finset.range r, Real.sqrt |M (X/u j)| ≤
      C*Real.sqrt ((X/Q:ℕ):ℝ)*Real.exp (-c*Real.sqrt (Real.log ((X/Q:ℕ):ℝ)))) :
    let N := X/Q
    let K := blockKernel (Finset.range r) u (blockVM u) X
    Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n)) ≤
      (2*(Real.log 4+4)+1)*C*Real.sqrt (N:ℝ)*(Q:ℝ)^(1-c/A) := by
  let N := X/Q
  have h := (arithmetic_fourier_kernel_rank_cost (Finset.range r) u (blockVM u) X Q hQ
    (fun j _ => h0 ▸ hu (Nat.zero_le j))).2
  dsimp only at *
  apply h.trans
  let e := Real.exp (-c*Real.sqrt (Real.log (N:ℝ)))
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : e ≤ (Q:ℝ)^(-c/A) := by
    rw [Real.rpow_def_of_pos hQr]
    apply Real.exp_le_exp.mpr
    have hle := mul_le_mul_of_nonneg_left hrange (show 0≤c/A by positivity)
    have hh : (c/A)*(A*Real.sqrt (Real.log (N:ℝ))) = c*Real.sqrt (Real.log (N:ℝ)) := by
      field_simp
    rw [hh] at hle
    rw [neg_div]
    nlinarith only [hle]
  calc
    _ ≤ ∑ j ∈ Finset.range r,|blockVM u j| * (C*Real.sqrt (N:ℝ)*e) := by
      refine Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hM j hj) (abs_nonneg _))
    _ = (∑ j ∈ Finset.range r,|blockVM u j|)*(C*Real.sqrt (N:ℝ)*e) := (Finset.sum_mul ..).symm
    _ ≤ ((2*(Real.log 4+4)+1)*(Q:ℝ))*(C*Real.sqrt (N:ℝ)*e) :=
      mul_le_mul_of_nonneg_right (dyadic_block_discrepancy_l1 Q r u hu h0 hr) (by dsimp [e]; positivity)
    _ ≤ ((2*(Real.log 4+4)+1)*(Q:ℝ))*(C*Real.sqrt (N:ℝ)*(Q:ℝ)^(-c/A)) := by
      have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
      gcongr
    _ = _ := by
      rw [show 1-c/A=1+( -c/A) by ring,Real.rpow_add hQr,Real.rpow_one]
      ring

end RHConnections.RankPairing
