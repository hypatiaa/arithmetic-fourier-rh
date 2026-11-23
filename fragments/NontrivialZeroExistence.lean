import Verified
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

open Filter
noncomputable section
namespace RHConnections.SpectralTail
open CanonicalFactor

theorem entireXi_at_two : entireXi 2 = (Real.pi:ℂ)/3 := by
  have h := (entireXi_zeta_germ (s := 2) (by norm_num) (by norm_num)).eq_of_nhds
  rw [h,riemannZeta_two,Complex.Gammaℝ]
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : (2:ℂ)/2=1 := by norm_num
  rw [hg,Complex.Gamma_one]
  norm_num [Complex.cpow_neg_one]
  field_simp [hp]
  <;> ring

theorem nontrivial_zeta_zero_nonempty : Nonempty NontrivialZetaZero := by
  by_contra! h
  letI : IsEmpty NontrivialZetaZero := h
  obtain ⟨B,hB⟩ := zeta_hadamard_factorization
  have hX (s : ℂ) : entireXi s=Complex.exp (B*s) := by
    rw [hB,zetaCanonicalProduct,tprod_empty,mul_one]
  have hE : (fun s : ℂ => Complex.exp (B*(1-s))) = (fun s : ℂ => Complex.exp (B*s)) := by
    ext1 s
    rw [← hX,← hX,entireXi_reflection]
  have hD₀ : HasDerivAt (fun s : ℂ => Complex.exp (B*(1-s)))
      (Complex.exp (B*(1-(0:ℂ)))*(B*(0-1))) 0 := by
    exact (((hasDerivAt_const (0:ℂ) (1:ℂ)).sub (hasDerivAt_id 0)).const_mul B).cexp
  have hD₁ : HasDerivAt (fun s : ℂ => Complex.exp (B*s)) (Complex.exp (B*0)*(B*1)) 0 :=
    ((hasDerivAt_id (0:ℂ)).const_mul B).cexp
  have hexp : Complex.exp B=1 := by
    have he := congrFun hE 0
    simpa only [sub_zero,mul_one,mul_zero,Complex.exp_zero] using he
  have hder := hD₀.deriv.symm.trans ((congrArg (fun g => deriv g 0) hE).trans hD₁.deriv)
  simp only [sub_zero,mul_one,mul_zero,Complex.exp_zero,hexp,one_mul,zero_sub,mul_neg] at hder
  have hB0 : B=0 := by linear_combination -(1/2:ℂ)*hder
  have hval := hX 2
  rw [entireXi_at_two,hB0,zero_mul,Complex.exp_zero] at hval
  have hreal := congrArg Complex.re hval
  norm_num [Complex.div_re] at hreal
  linarith [Real.pi_gt_three]

end RHConnections.SpectralTail
