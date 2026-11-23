import Verified

noncomputable section
namespace RHConnections.PerronRamp
open ArithmeticFunction

private abbrev mangoldtCoeff (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℝ)

def sharpChebyshev (X : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)

def smoothedChebyshev (h X : ℝ) : ℂ :=
  ∑' n : ℕ, mangoldtCoeff n * (ramp h (Real.log X-Real.log n) : ℂ)

theorem smoothedChebyshev_error {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ‖smoothedChebyshev h X - sharpChebyshev X‖ ≤ 3*(X*h+1)*(1+Real.log X) := by
  classical
  let L := X*Real.exp (-h)
  let U := X*Real.exp h
  let T := Finset.Icc 1 ⌊U⌋₊
  let J := Finset.Ioc ⌊L⌋₊ ⌊U⌋₊
  let A (n : ℕ) := mangoldtCoeff n * (ramp h (Real.log X-Real.log n) : ℂ)
  let D (n : ℕ) := if n ∈ Finset.Icc 1 ⌊X⌋₊ then mangoldtCoeff n else 0
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
  have hA : smoothedChebyshev h X = ∑ n ∈ T, A n := by
    apply tsum_eq_sum
    intro n hn
    by_cases hn₀ : n = 0
    · subst n
      simp [A,mangoldtCoeff]
    · apply hupper
      exact lt_of_not_ge (fun hle => hn (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn₀, hle⟩))
  have hT : Finset.Icc 1 ⌊X⌋₊ ⊆ T := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hU)⟩
  have hD : sharpChebyshev X = ∑ n ∈ T, D n := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, D n := Finset.sum_congr rfl (fun n hn => by simp only [D,if_pos hn])
      _ = _ := Finset.sum_subset hT (fun n _ hn => by simp only [D,if_neg hn])
  have hJ : J ⊆ T := fun n hn =>
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,(Finset.mem_Ioc.mp hn).2⟩
  have hdiff : smoothedChebyshev h X-sharpChebyshev X = ∑ n ∈ J, (A n-D n) := by
    rw [hA,hD,← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset hJ
    intro n hn hnJ
    have hn' := Finset.mem_Icc.mp hn
    have hnl : n ≤ ⌊L⌋₊ := le_of_not_gt (fun h => hnJ (Finset.mem_Ioc.mpr ⟨h,hn'.2⟩))
    exact sub_eq_zero.mpr (hlower n hn'.1 hnl)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hB : 0 ≤ 1+Real.log X := by linarith
  have hcoeff (n : ℕ) (hn : n ∈ J) : ‖mangoldtCoeff n‖ ≤ 1+Real.log X := by
    have hnT := Finset.mem_Icc.mp (hJ hn)
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog := Real.log_le_log hn' ((Nat.le_floor_iff hu.le).mp hnT.2)
    have hUlog : Real.log U = Real.log X+h := by
      dsimp only [U]
      rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [hUlog] at hlog
    change ‖((ArithmeticFunction.vonMangoldt n : ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)]
  have herr (n : ℕ) (hnJ : n ∈ J) : ‖A n-D n‖ ≤ 1+Real.log X := by
    let r := ramp h (Real.log X-Real.log n)
    have hr : 0 ≤ r ∧ r ≤ 1 := ramp_mem_Icc hh _
    by_cases hn : n ∈ Finset.Icc 1 ⌊X⌋₊
    · change ‖mangoldtCoeff n * (r:ℂ) - (if n ∈ Finset.Icc 1 ⌊X⌋₊ then mangoldtCoeff n else 0)‖ ≤ 1+Real.log X
      rw [if_pos hn, ← mul_sub_one, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real (r-1), Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hr.2)]
      exact (mul_le_mul (hcoeff n hnJ) (by linarith : -(r-1) ≤ 1) (by linarith) hB).trans_eq (mul_one _)
    · change ‖mangoldtCoeff n * (r:ℂ) - (if n ∈ Finset.Icc 1 ⌊X⌋₊ then mangoldtCoeff n else 0)‖ ≤ 1+Real.log X
      rw [if_neg hn, sub_zero, norm_mul, Complex.norm_of_nonneg hr.1]
      simpa only [mul_one] using mul_le_mul (hcoeff n hnJ) hr.2 hr.1 hB
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
    _ ≤ ∑ _n ∈ J, (1+Real.log X) := Finset.sum_le_sum herr
    _ = ((⌊U⌋₊:ℝ)-(⌊L⌋₊:ℝ))*(1+Real.log X) := by
      simp [J,Nat.cast_sub (Nat.floor_mono (hL.trans hU)),nsmul_eq_mul] <;> ring
    _ ≤ 3*(X*h+1)*(1+Real.log X) := mul_le_mul_of_nonneg_right
      (by linarith [Nat.floor_le hu.le,Nat.lt_floor_add_one L]) hB

#print axioms smoothedChebyshev_error
end RHConnections.PerronRamp
