import RelativeResolvent
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

open MeasureTheory Set
namespace RHConnections.RelativeResolvent

theorem laplace_difference (z z₀ xi : ℂ)
    (hz : xi.re < z.re) (hz₀ : xi.re < z₀.re) :
    (∫ x : ℝ in Ioi 0,
      Complex.exp ((xi-z)*(x : ℂ)) - Complex.exp ((xi-z₀)*(x : ℂ))) =
      relative z z₀ xi := by
  have h1 : (xi-z).re < 0 := by simp only [Complex.sub_re]; linarith
  have h2 : (xi-z₀).re < 0 := by simp only [Complex.sub_re]; linarith
  rw [integral_sub (integrableOn_exp_mul_complex_Ioi h1 0)
      (integrableOn_exp_mul_complex_Ioi h2 0),
    integral_exp_mul_complex_Ioi h1 0, integral_exp_mul_complex_Ioi h2 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show xi-z = -(z-xi) by ring, show xi-z₀ = -(z₀-xi) by ring]
  unfold relative
  simp only [neg_div_neg_eq, one_div]

#print axioms laplace_difference
end RHConnections.RelativeResolvent
