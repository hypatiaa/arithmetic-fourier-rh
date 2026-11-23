import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RHConnections.StripEvaluationWitness

def witness (n : ℕ) (lam z : ℂ) := Complex.exp ((n:ℂ)*(z-lam)+(z-lam)^2)
def gaussianMass : ℝ := ∫ y : ℝ, Real.exp (-2*y^2)
def lineMass (n : ℕ) (lam : ℂ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, ‖witness n lam ⟨x,y⟩‖^2

theorem witness_entire (n : ℕ) (lam : ℂ) : Differentiable ℂ (witness n lam) := by
  unfold witness
  fun_prop

@[simp] theorem witness_at (n : ℕ) (lam : ℂ) : witness n lam lam = 1 := by simp [witness]

private theorem witness_sq (n : ℕ) (lam : ℂ) (x y : ℝ) : ‖witness n lam ⟨x,y⟩‖^2 =
      Real.exp (2*(n:ℝ)*(x-lam.re) + 2*(x-lam.re)^2) * Real.exp (-2*(y+(-lam.im))^2) := by
    rw [witness,Complex.norm_exp,pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    simp only [Complex.add_re, pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.natCast_re, Complex.natCast_im]
    ring

theorem witness_line_integrable (n : ℕ) (lam : ℂ) (x : ℝ) :
    Integrable (fun y : ℝ => ‖witness n lam ⟨x,y⟩‖^2) := by
  simp_rw [witness_sq]
  exact ((integrable_exp_neg_mul_sq (by norm_num : 0 < (2:ℝ))).comp_add_right (-lam.im)).const_mul _

theorem gaussianMass_eq : gaussianMass = Real.sqrt (Real.pi/2) := integral_gaussian 2

theorem lineMass_exact (n : ℕ) (lam : ℂ) (x : ℝ) :
    lineMass n lam x = gaussianMass *
      Real.exp (2*(n:ℝ)*(x-lam.re) + 2*(x-lam.re)^2) := by
  let B := 2*(n:ℝ)*(x-lam.re) + 2*(x-lam.re)^2
  unfold lineMass
  simp_rw [witness_sq]
  rw [integral_const_mul, show (∫ y : ℝ, Real.exp (-2*(y+(-lam.im))^2)) = gaussianMass from
    integral_add_right_eq_self (fun y : ℝ => Real.exp (-2*y^2)) (-lam.im)]
  ring

theorem lineMass_le {a : ℝ} {lam : ℂ} (_hgap : a < lam.re) (n : ℕ) {x : ℝ} (hx : |x| ≤ a) :
    lineMass n lam x ≤ gaussianMass *
      Real.exp (-2*(n:ℝ)*(lam.re-a)+2*(a+|lam.re|)^2) := by
  have ha := (abs_nonneg x).trans hx
  have hdist : |x-lam.re| ≤ a+|lam.re| :=
    (by simpa only [Real.norm_eq_abs] using norm_sub_le x lam.re :
      |x-lam.re| ≤ |x|+|lam.re|).trans (add_le_add hx le_rfl)
  have hsq : (x-lam.re)^2 ≤ (a+|lam.re|)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdist 2
  rw [lineMass_exact]
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _ => (Real.exp_pos _).le)
  apply Real.exp_le_exp.mpr
  have hlin := mul_le_mul_of_nonneg_left ((le_abs_self x).trans hx) (Nat.cast_nonneg (α := ℝ) n)
  nlinarith

theorem lineMass_uniformly_small {a : ℝ} {lam : ℂ} (hgap : a < lam.re) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ x : ℝ, |x| ≤ a → lineMass n lam x < ε := by
  have hneg : -(2*(lam.re-a)) < 0 := by linarith
  have ht : Tendsto (fun n : ℕ => -(2*(lam.re-a))*(n:ℝ)) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop hneg tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => gaussianMass *
      Real.exp (-2*(n:ℝ)*(lam.re-a)+2*(a+|lam.re|)^2)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp ht
    have he' := he.const_mul (gaussianMass * Real.exp (2*(a+|lam.re|)^2))
    simp only [mul_zero] at he'
    refine he'.congr' (Eventually.of_forall fun n => ?_)
    change (gaussianMass * Real.exp (2*(a+|lam.re|)^2)) *
      Real.exp (-(2*(lam.re-a))*(n:ℝ)) = gaussianMass *
        Real.exp (-2*(n:ℝ)*(lam.re-a)+2*(a+|lam.re|)^2)
    rw [Real.exp_add]
    ring_nf
  intro ε hε
  filter_upwards [hlim.eventually_lt_const hε] with n hn
  exact fun x hx => (lineMass_le hgap n hx).trans_lt hn

#print axioms witness_at
#print axioms lineMass_exact
#print axioms lineMass_uniformly_small
end RHConnections.StripEvaluationWitness
