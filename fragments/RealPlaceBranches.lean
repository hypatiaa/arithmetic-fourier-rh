import Verified

namespace RHConnections.PoleCompensation
open ArchimedeanLimit

theorem parityRealPlaceKernel_branch_formula (odd : Bool) {x : ℝ} (hx : 0 < x) :
    parityRealPlaceKernel odd x =
      Real.exp (x/2)/2 * (1/(Real.exp x - 1) +
        (if odd then (-1:ℝ) else 1)/(Real.exp x + 1)) := by
  have he : 1 < Real.exp x := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hx
  have he0 := (Real.exp_pos x).ne'
  have heM : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr he.ne'
  have heP : Real.exp x + 1 ≠ 0 := by positivity
  have hehalf : Real.exp (x/2)^2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add, show x/2+x/2=x by ring]
  have hehalf0 := (Real.exp_pos (x/2)).ne'
  have h2 : Real.exp (-2*x) = (Real.exp x ^ 2)⁻¹ := by
    rw [show -2*x = -(x+x) by ring, Real.exp_neg, Real.exp_add, pow_two]
  have hD : 1 - (Real.exp x ^ 2)⁻¹ ≠ 0 := by
    rw [← h2]
    have h : Real.exp (-2*x) < 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_lt_exp.mpr
      linarith
    exact sub_ne_zero.mpr h.ne'
  have hh : Real.exp (-x/2) = (Real.exp (x/2))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  let y := Real.exp (x/2)
  have hy : 0 < y := Real.exp_pos _
  have hy2 : 1 < y^2 := by dsimp [y]; rw [hehalf]; exact he
  have hyM : y^2-1 ≠ 0 := sub_ne_zero.mpr hy2.ne'
  have hyP : y^2+1 ≠ 0 := by positivity
  have hyD : 1 - ((y^2)^2)⁻¹ ≠ 0 := by
    change 1 - ((Real.exp (x/2)^2)^2)⁻¹ ≠ 0
    rwa [hehalf]
  have hyD' : -1+y^4 ≠ 0 := by
    have hpow : (1:ℝ)^2 < (y^2)^2 := pow_lt_pow_left₀ hy2 zero_le_one (by decide)
    rw [one_pow, ← pow_mul] at hpow
    norm_num at hpow
    linarith
  cases odd
  · rw [parityRealPlaceKernel_even, realPlaceKernel, h2, hh, ← hehalf]
    simp only [Bool.false_eq_true, if_false]
    change y⁻¹/(1-((y^2)^2)⁻¹) = y/2*(1/(y^2-1)+1/(y^2+1))
    field_simp [hy.ne', hyM, hyP, hyD, hyD'] <;> ring_nf <;> field_simp [hyD'] <;> ring
  · rw [parityRealPlaceKernel_odd, realPlaceKernel, h2, hh, Real.exp_neg, ← hehalf]
    simp only [if_true]
    change (y^2)⁻¹*(y⁻¹/(1-((y^2)^2)⁻¹)) = y/2*(1/(y^2-1)+(-1)/(y^2+1))
    field_simp [hy.ne', hyM, hyP, hyD, hyD'] <;> ring_nf <;> field_simp [hyD'] <;> ring

end RHConnections.PoleCompensation
