import Verified

open MeasureTheory Filter
noncomputable section
namespace RHConnections.PoleCompensation
open ArchimedeanLimit RelativeResolvent

private def archWeight (k : ℕ) (x : ℝ) := Real.exp (-((1/2 : ℝ) + 2*k)*x)

private theorem archWeight_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun k => archWeight k x) (realPlaceKernel x) := by
  have he : Real.exp (-2*x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (hasSum_geometric_of_lt_one (Real.exp_pos (-2*x)).le he).mul_left (Real.exp (-x/2))
  have ht (k : ℕ) : Real.exp (-x/2) * Real.exp (-2*x)^k = archWeight k x := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    unfold archWeight
    congr 1
    ring
  have hs' := hs.congr_fun (g := fun k => archWeight k x) (fun k => (ht k).symm)
  simpa only [realPlaceKernel, div_eq_mul_inv] using hs'

private theorem archWeight_laplace (k : ℕ) {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    (∫ x in Set.Ioi (0 : ℝ), (archWeight k x : ℂ) * logTest z z₀ x) =
      (z+1/2+2*k)⁻¹ - (z₀+1/2+2*k)⁻¹ := by
  let a : ℝ := (1/2 : ℝ) + 2*k
  have ha : 0 < a := by dsimp [a]; positivity
  have h1 : (-(a : ℂ)).re < z.re := by simp only [Complex.neg_re, Complex.ofReal_re]; linarith
  have h2 : (-(a : ℂ)).re < z₀.re := by simp only [Complex.neg_re, Complex.ofReal_re]; linarith
  calc
    _ = ∫ x : ℝ in Set.Ioi 0, Complex.exp ((-(a : ℂ)-z)*(x : ℂ)) -
          Complex.exp ((-(a : ℂ)-z₀)*(x : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hcast : (archWeight k x : ℂ) = Complex.exp (-(a : ℂ)*(x : ℂ)) := by
        unfold archWeight
        rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
      change (archWeight k x : ℂ) * logTest z z₀ x =
        Complex.exp ((-(a : ℂ)-z)*(x : ℂ)) - Complex.exp ((-(a : ℂ)-z₀)*(x : ℂ))
      rw [hcast, logTest, if_pos (show 0 < x from hx), mul_sub, ← Complex.exp_add, ← Complex.exp_add]
      congr 2 <;> ring
    _ = relative z z₀ (-(a : ℂ)) := laplace_difference z z₀ _ h1 h2
    _ = _ := by
      simp only [relative, sub_neg_eq_add, a, Complex.ofReal_add, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_natCast]
      simp only [add_assoc]

theorem realPlaceRelative_hasSum {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    HasSum (fun k : ℕ => (z+1/2+2*k)⁻¹ - (z₀+1/2+2*k)⁻¹) (realPlaceRelative z z₀) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F (k : ℕ) (x : ℝ) := (archWeight k x : ℂ) * logTest z z₀ x
  let B (k : ℕ) (x : ℝ) := archWeight k x * ‖logTest z z₀ x‖
  have hpos : ∀ᵐ x ∂μ, 0 < x := ae_restrict_mem (μ := volume) measurableSet_Ioi
  have hB (x : ℝ) (hx : 0 < x) : HasSum (fun k => B k x)
      (realPlaceKernel x * ‖logTest z z₀ x‖) := (archWeight_hasSum hx).mul_right _
  have hmeas : Measurable realPlaceKernel := by unfold realPlaceKernel; fun_prop
  have hD : Integrable (fun x : ℝ => 4 * Real.exp (-(1/4 : ℝ)*x)) μ :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1/4 : ℝ) < 0) 0).const_mul 4
  have hi : Integrable (fun x : ℝ => realPlaceKernel x * ‖logTest z z₀ x‖) μ := by
    apply (hD.mul_const (‖z‖ + ‖z₀‖)).mono'
      (hmeas.aestronglyMeasurable.mul (logTest_continuous z z₀).norm.aestronglyMeasurable)
    filter_upwards [hpos] with x hx
    change ‖realPlaceKernel x * ‖logTest z z₀ x‖‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (realPlaceKernel_nonneg hx) (norm_nonneg _))]
    calc
      _ ≤ realPlaceKernel x * ((‖z‖+‖z₀‖)*x) := mul_le_mul_of_nonneg_left
        (logTest_linear hz hz₀ hx.le) (realPlaceKernel_nonneg hx)
      _ = (realPlaceKernel x*x)*(‖z‖+‖z₀‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (realPlaceKernel_mul_x_bound hx) (by positivity)
  have hs : HasSum (fun k => ∫ x, F k x ∂μ) (realPlaceRelative z z₀) := by
    apply hasSum_integral_of_dominated_convergence (μ := μ) (F := F)
      (f := fun x => (realPlaceKernel x : ℂ) * logTest z z₀ x) B
    · intro k
      have hc : Continuous (fun x : ℝ => (archWeight k x : ℂ)) := by unfold archWeight; fun_prop
      exact (hc.mul (logTest_continuous z z₀)).aestronglyMeasurable
    · intro k
      exact Eventually.of_forall fun x => by
        simp only [F, B, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, le_refl, archWeight]
    · exact hpos.mono fun x hx => (hB x hx).summable
    · exact hi.congr (hpos.mono fun x hx => (hB x hx).tsum_eq.symm)
    · exact hpos.mono fun x hx => (Complex.hasSum_ofReal.mpr (archWeight_hasSum hx)).mul_right _
  exact hs.congr_fun fun k => (archWeight_laplace k hz hz₀).symm

theorem realPlaceRelative_eq_tsum {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    realPlaceRelative z z₀ = ∑' k : ℕ, ((z+1/2+2*k)⁻¹ - (z₀+1/2+2*k)⁻¹) :=
  (realPlaceRelative_hasSum hz hz₀).tsum_eq.symm

#print axioms realPlaceRelative_hasSum
#print axioms realPlaceRelative_eq_tsum
end RHConnections.PoleCompensation
