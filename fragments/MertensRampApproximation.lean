import Verified

noncomputable section
namespace RHConnections.PerronRamp
open MertensCriterion

def smoothedMertens (h X : ℝ) : ℂ :=
  ∑' n : ℕ, moebiusCoeff n * (ramp h (Real.log X-Real.log n) : ℂ)

theorem smoothedMertens_error {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ‖smoothedMertens h X - mertens X‖ ≤ 3*(X*h+1) := by
  classical
  let L := X*Real.exp (-h)
  let U := X*Real.exp h
  let T := Finset.Icc 1 ⌊U⌋₊
  let J := Finset.Ioc ⌊L⌋₊ ⌊U⌋₊
  let A (n : ℕ) := moebiusCoeff n * (ramp h (Real.log X-Real.log n) : ℂ)
  let D (n : ℕ) := if n ∈ Finset.Icc 1 ⌊X⌋₊ then moebiusCoeff n else 0
  have hx : 0 < X := by linarith
  have hl : 0 < L := mul_pos hx (Real.exp_pos _)
  have hL : L ≤ X := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh.le)) hx.le
  have hU : X ≤ U := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hh.le) hx.le
  have hu : 0 < U := hx.trans_le hU
  have hupper (n : ℕ) (hn : ⌊U⌋₊ < n) : A n = 0 := by
    have hnU : U < (n:ℝ) := (Nat.floor_lt hu.le).mp hn
    have hlog := Real.log_le_log hu hnU.le
    have hUlog : Real.log U = Real.log X+h := by
      dsimp only [U]
      rw [Real.log_mul hx.ne' (Real.exp_pos _).ne',Real.log_exp]
    rw [hUlog] at hlog
    simp [A, ramp_zero hh (show Real.log X-Real.log n ≤ -h by linarith)]
  have hlower (n : ℕ) (hn : 1 ≤ n) (hnL : n ≤ ⌊L⌋₊) : A n = D n := by
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog := Real.log_le_log hn' ((Nat.le_floor_iff hl.le).mp hnL)
    have hLlog : Real.log L = Real.log X-h := by
      dsimp only [L]
      rw [Real.log_mul hx.ne' (Real.exp_pos _).ne',Real.log_exp]
      ring
    rw [hLlog] at hlog
    have hm : n ∈ Finset.Icc 1 ⌊X⌋₊ := Finset.mem_Icc.mpr ⟨hn,hnL.trans (Nat.floor_mono hL)⟩
    simp only [A,D,if_pos hm,ramp_one hh (show h ≤ Real.log X-Real.log n by linarith),Complex.ofReal_one,mul_one]
  have hA : smoothedMertens h X = ∑ n ∈ T, A n := by
    apply tsum_eq_sum
    intro n hn
    by_cases hn₀ : n = 0
    · subst n
      simp [A,moebiusCoeff]
    · apply hupper
      exact lt_of_not_ge (fun hle => hn (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn₀, hle⟩))
  have hT : Finset.Icc 1 ⌊X⌋₊ ⊆ T := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hU)⟩
  have hD : mertens X = ∑ n ∈ T, D n := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, D n := Finset.sum_congr rfl (fun n hn => by simp only [D,if_pos hn])
      _ = _ := Finset.sum_subset hT (fun n _ hn => by simp only [D,if_neg hn])
  have hJ : J ⊆ T := fun n hn =>
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,(Finset.mem_Ioc.mp hn).2⟩
  have hdiff : smoothedMertens h X-mertens X = ∑ n ∈ J, (A n-D n) := by
    rw [hA,hD,← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset hJ
    intro n hn hnJ
    have hn' := Finset.mem_Icc.mp hn
    have hnl : n ≤ ⌊L⌋₊ := le_of_not_gt (fun h => hnJ (Finset.mem_Ioc.mpr ⟨h,hn'.2⟩))
    exact sub_eq_zero.mpr (hlower n hn'.1 hnl)
  have hcoeff (n : ℕ) : ‖moebiusCoeff n‖ ≤ 1 := by
    rw [moebiusCoeff,Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have herr (n : ℕ) : ‖A n-D n‖ ≤ 1 := by
    let r := ramp h (Real.log X-Real.log n)
    have hr : 0 ≤ r ∧ r ≤ 1 := ramp_mem_Icc hh _
    by_cases hn : n ∈ Finset.Icc 1 ⌊X⌋₊
    · change ‖moebiusCoeff n * (r:ℂ) - (if n ∈ Finset.Icc 1 ⌊X⌋₊ then moebiusCoeff n else 0)‖ ≤ 1
      rw [if_pos hn, ← mul_sub_one, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hr.2)]
      exact (mul_le_mul (hcoeff n) (by linarith : -(r-1) ≤ 1) (by linarith) zero_le_one).trans_eq (one_mul _)
    · change ‖moebiusCoeff n * (r:ℂ) - (if n ∈ Finset.Icc 1 ⌊X⌋₊ then moebiusCoeff n else 0)‖ ≤ 1
      rw [if_neg hn, sub_zero, norm_mul, Complex.norm_of_nonneg hr.1]
      simpa only [one_mul] using mul_le_mul (hcoeff n) hr.2 hr.1 zero_le_one
  have hwidth : U-L ≤ 3*(X*h) := by
    have hep := Real.abs_exp_sub_one_le (show |h| ≤ 1 by simpa [abs_of_pos hh] using hh₁)
    have hp' := (le_abs_self (Real.exp h-1)).trans hep
    rw [abs_of_pos hh] at hp'
    have he' := Real.add_one_le_exp (-h)
    calc
      _ = X*(Real.exp h-Real.exp (-h)) := by dsimp [U,L]; ring
      _ ≤ X*(3*h) := mul_le_mul_of_nonneg_left (by linarith) hx.le
      _ = _ := by ring
  rw [hdiff]
  calc
    _ ≤ ∑ n ∈ J, ‖A n-D n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ J, (1:ℝ) := Finset.sum_le_sum (fun n _ => herr n)
    _ = (⌊U⌋₊:ℝ) - (⌊L⌋₊:ℝ) := by
      simp [J,Nat.cast_sub (Nat.floor_mono (hL.trans hU))]
    _ ≤ 3*(X*h+1) := by linarith [Nat.floor_le hu.le,Nat.lt_floor_add_one L]

#print axioms smoothedMertens_error
end RHConnections.PerronRamp
