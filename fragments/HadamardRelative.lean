import Verified

open Filter
namespace RHConnections.CanonicalFactor
open SpectralTail RelativeResolvent PoleCompensation

def ZetaHadamardFactorization : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, entireXi s = Complex.exp (B*s) * zetaCanonicalProduct s

theorem entireXi_logDerivative_of_hadamard {B : ℂ}
    (hB : ∀ s : ℂ, entireXi s = Complex.exp (B*s) * zetaCanonicalProduct s)
    {s : ℂ} (hs : ∀ r : NontrivialZetaZero, s ≠ r.val) :
    logDeriv entireXi s = B + logDeriv zetaCanonicalProduct s := by
  have he : entireXi = fun t : ℂ => Complex.exp (B*t)*zetaCanonicalProduct t :=
    funext hB
  have hd : HasDerivAt (fun t : ℂ => Complex.exp (B*t))
      (Complex.exp (B*s)*B) s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul B).cexp
  rw [he, logDeriv_fun_mul (f := fun t : ℂ => Complex.exp (B*t)) (g := zetaCanonicalProduct)
    s (Complex.exp_ne_zero _) (zetaCanonicalProduct_ne_zero hs)
    hd.differentiableAt (zetaCanonicalProduct_entire s (Set.mem_univ s)).differentiableAt,
    logDeriv_apply (fun t : ℂ => Complex.exp (B*t)), hd.deriv]
  rw [mul_comm (Complex.exp (B*s)) B, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]

theorem entireXi_relative_logDerivative (h : ZetaHadamardFactorization)
    {s s₀ : ℂ} (hs : ∀ r : NontrivialZetaZero, s ≠ r.val)
    (hs₀ : ∀ r : NontrivialZetaZero, s₀ ≠ r.val) :
    HasSum (fun r : RepeatedZetaZero => relative s s₀ r.1.val)
      (logDeriv entireXi s - logDeriv entireXi s₀) := by
  obtain ⟨B,hB⟩ := h
  rw [entireXi_logDerivative_of_hadamard hB hs, entireXi_logDerivative_of_hadamard hB hs₀]
  simpa using zetaCanonicalProduct_relative_logDerivative hs hs₀

theorem zetaSpectralRelative_eq_logDerivative (h : ZetaHadamardFactorization)
    {z z₀ : ℂ} (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    zetaSpectralRelative z z₀ =
      logDeriv entireXi (z+1/2) - logDeriv entireXi (z₀+1/2) := by
  have hh (w : ℂ) (hw : 1/2 < w.re) (r : NontrivialZetaZero) : w+1/2 ≠ r.val := by
    intro he
    have h := congrArg Complex.re he
    have ht := r.property.1.2
    norm_num [Complex.add_re, Complex.div_re] at h
    linarith
  have hSum := entireXi_relative_logDerivative h (hh z hz) (hh z₀ hz₀)
  rw [← hSum.tsum_eq, hSum.summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  unfold zetaSpectralRelative
  apply tsum_congr
  intro r
  have he (v : ℂ) : (v+(1/2:ℂ))-r.val = v-(r.val-1/2) := by ring
  simp only [relative, he, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end RHConnections.CanonicalFactor
