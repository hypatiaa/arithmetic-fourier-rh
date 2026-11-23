import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

noncomputable section
namespace RHConnections.GammaSeqLogDerivative

private theorem factor_ne {s : ℂ} (hs : 0 < s.re) (j : ℕ) : s + j ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
  linarith [Nat.cast_nonneg (α := ℝ) j]

private theorem denominator_ne {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∏ j ∈ Finset.range (n+1), (s+j)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne hs j

theorem gammaSeq_differentiableOn {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun w : ℂ => Complex.GammaSeq w n) {w : ℂ | 0 < w.re} := by
  intro s hs
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  apply DifferentiableAt.differentiableWithinAt
  simp only [Complex.GammaSeq, Complex.cpow_def_of_ne_zero hn']
  exact (show DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.log (n : ℂ)*w) *
    (n.factorial : ℂ)) s by fun_prop).div
    (show DifferentiableAt ℂ (fun w : ℂ => ∏ j ∈ Finset.range (n+1), (w+j)) s by fun_prop)
    (denominator_ne hs n)

theorem gammaSeq_logDeriv {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun w : ℂ => Complex.GammaSeq w n) s =
      Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n+1), (s+j)⁻¹ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [Complex.GammaSeq, Complex.cpow_def_of_ne_zero hn']
  rw [logDeriv_fun_div (f := fun w : ℂ => Complex.exp (Complex.log (n : ℂ)*w) * (n.factorial : ℂ)) (g := fun w : ℂ => ∏ j ∈ Finset.range (n+1), (w+j)) s (mul_ne_zero (Complex.exp_ne_zero _) hf) (denominator_ne hs n)
    (by fun_prop) (by fun_prop), logDeriv_mul_const s _ hf,
    logDeriv_fun_prod (s := Finset.range (n+1)) (f := fun (j : ℕ) (w : ℂ) => w+j) (fun j _ => factor_ne hs j) (by intros; fun_prop)]
  congr 1
  · have hd : HasDerivAt (fun w : ℂ => Complex.exp (Complex.log (n : ℂ) * w))
        (Complex.exp (Complex.log (n : ℂ) * s) * Complex.log (n : ℂ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (Complex.log (n : ℂ))).cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp
  · apply Finset.sum_congr rfl
    intro j hj
    have hjd : HasDerivAt (fun w : ℂ => w + (j : ℂ)) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const (j : ℂ)
    rw [logDeriv_apply, hjd.deriv]
    simp

end RHConnections.GammaSeqLogDerivative
