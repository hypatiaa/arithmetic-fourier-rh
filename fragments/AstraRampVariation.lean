import Verified
open Filter Set MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace RHConnections.SharpRadialTail
open SmoothedPrimeSandwichUniform SmoothedPrimeLimit SpectralTail

theorem shell_variation {a b h : ℝ} (hh : 0 < h) :
    (∫ x in (0:ℝ)..3, ‖deriv (shell a b h) x‖) ≤ 2 := by
  let R (c x : ℝ) := step ((x-c)/h)
  have hR (c : ℝ) : ContDiff ℝ ∞ (R c) := by
    have haff : ContDiff ℝ ∞ (fun x : ℝ => (x-c)/h) := by fun_prop
    exact Real.smoothTransition.contDiff.comp haff
  have hD (c : ℝ) : Differentiable ℝ (R c) := (hR c).differentiable (by simp)
  have hC (c : ℝ) : Continuous (deriv (R c)) := (contDiff_infty_iff_deriv.mp (hR c)).2.continuous
  have hm (c : ℝ) : Monotone (R c) := fun x y hxy =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy c) hh.le)
  have hpos (c x : ℝ) : 0 ≤ deriv (R c) x := (hm c).deriv_nonneg
  have hform (x : ℝ) : deriv (shell a b h) x = deriv (R a) x - deriv (R b) x :=
    ((hD a x).hasDerivAt.sub (hD b x).hasDerivAt).deriv
  have hI (c : ℝ) : (∫ x in (0:ℝ)..3, deriv (R c) x) ≤ 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hD c x) ((hC c).intervalIntegrable _ _)]
    exact (sub_le_self _ (Real.smoothTransition.nonneg _)).trans (Real.smoothTransition.le_one _)
  calc
    _ ≤ ∫ x in (0:ℝ)..3, (deriv (R a) x + deriv (R b) x) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((contDiff_infty_iff_deriv.mp (shell_smooth a b h)).2.continuous.norm.intervalIntegrable _ _)
        (((hC a).add (hC b)).intervalIntegrable _ _)
      intro x _
      simpa only [hform,Pi.add_apply,Real.norm_of_nonneg (hpos _ _)] using
        norm_sub_le (deriv (R a) x) (deriv (R b) x)
    _ ≤ _ := by rw [intervalIntegral.integral_add ((hC a).intervalIntegrable _ _) ((hC b).intervalIntegrable _ _)]; linarith [hI a,hI b]

private theorem transfer (z : ℂ) {g g' : ℝ → ℂ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hc : Continuous g') (h0 : g 0 = 0) (h3 : g 3 = 0) :
    z * (∫ x in (0:ℝ)..3, Complex.exp (z*(x:ℂ))*g x) =
      -(∫ x in (0:ℝ)..3, Complex.exp (z*(x:ℂ))*g' x) := by
  let E := fun x : ℝ => Complex.exp (z*(x:ℂ))
  have hd (y : ℝ) : HasDerivAt E (z*E y) y := by
    simpa [E,mul_comm] using (((hasDerivAt_id (y:ℂ)).const_mul z).cexp).comp_ofReal
  have hE : Continuous (fun y => z*E y) := by unfold E; fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0:ℝ)) (b := 3) (fun x _ => hg x) (fun x _ => hd x)
    (hc.intervalIntegrable _ _) (hE.intervalIntegrable _ _)
  rw [h0,h3,zero_mul,zero_mul,sub_zero,zero_sub] at hi
  unfold E at hi
  rw [← intervalIntegral.integral_const_mul]
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hi

theorem spectral_first_majorant {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h)
    (ha : 0 < a) (hb : b+h < 3) (r : NontrivialZetaZero) :
    ‖compactZeroTerm (scaleTest 0 (fun x => (shell a b h x : ℂ))) r‖ ≤
    ((analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖) * (Real.exp 3 * 2) := by
  let f := shell a b h
  let z := r.val
  let E := fun x : ℝ => Complex.exp (z*(x:ℂ))
  have hs : ContDiff ℝ ∞ f := shell_smooth _ _ _
  have hs' := (contDiff_infty_iff_deriv.mp hs).2
  have hd := hs.differentiable (by simp)
  have h0 : f =ᶠ[𝓝 (0:ℝ)] (fun _ => 0) := by
    filter_upwards [eventually_lt_nhds ha] with x hx using shell_left hab hh hx.le
  have h3 : f =ᶠ[𝓝 (3:ℝ)] (fun _ => 0) := by
    filter_upwards [eventually_gt_nhds hb] with x hx using shell_right hab hh hx.le
  have h1 := transfer z (fun x => (hd x).hasDerivAt.ofReal_comp)
    (Complex.continuous_ofReal.comp hs'.continuous) (by simp [h0.eq_of_nhds])
    (by simp [h3.eq_of_nhds])
  have hei (x : ℝ) (hx : x ∈ Icc (0:ℝ) 3) : ‖E x‖ ≤ Real.exp 3 := by
    rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right r.property.1.2.le hx.1).trans (by simpa using hx.2)
  have hnorm : ‖∫ x in (0:ℝ)..3, E x*((deriv f x : ℝ):ℂ)‖ ≤ Real.exp 3 * 2 := by
    have hEc : Continuous E := by unfold E; fun_prop
    calc
      _ ≤ ∫ x in (0:ℝ)..3, ‖E x*((deriv f x : ℝ):ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ x in (0:ℝ)..3, Real.exp 3 * ‖deriv f x‖ := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((hEc.mul (Complex.continuous_ofReal.comp hs'.continuous)).norm.intervalIntegrable _ _)
          ((continuous_const.mul hs'.continuous.norm).intervalIntegrable _ _)
        intro x hx
        simp only [Pi.mul_apply,Function.comp_apply,norm_mul,Complex.norm_real]
        exact mul_le_mul_of_nonneg_right (hei x hx) (norm_nonneg _)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (shell_variation hh) (Real.exp_pos _).le
  have hI : (∫ x in Ioi (0:ℝ), E x*(f x:ℂ)) = ∫ x in (0:ℝ)..3, E x*(f x:ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => hx.1)
    intro x hx
    have hx3 : 3 < x := by by_contra! e; exact hx.2 ⟨hx.1,e⟩
    simp [f,shell_right hab hh (hb.trans hx3).le]
  have hm : compactZeroTerm (scaleTest 0 (fun x => (f x:ℂ))) r =
      (analyticOrderNatAt riemannZeta r.val:ℂ) * ∫ x in (0:ℝ)..3, E x*(f x:ℂ) := by
    rw [← hI]
    unfold compactZeroTerm
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [scaleTest,Complex.ofReal_zero,sub_zero,← mul_assoc,← Complex.exp_add,E,z]
    congr 2
    ring
  rw [show (fun x => (shell a b h x:ℂ)) = (fun x => (f x:ℂ)) from rfl,hm,norm_mul,Complex.norm_natCast]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro e; have hh' := r.property.1.1; change 0 < z.re at hh'; simp [e] at hh')

  have hv := congrArg norm h1
  rw [norm_mul,norm_neg] at hv
  have hB := (le_div_iff₀ hn).2 (by simpa only [mul_comm _ ‖z‖] using hv.le.trans hnorm)
  calc
    _ ≤ (analyticOrderNatAt riemannZeta r.val:ℝ) * ((Real.exp 3 * 2)/‖z‖) :=
      mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
    _ = _ := by unfold z; ring

#print axioms shell_variation
#print axioms spectral_first_majorant
end RHConnections.SharpRadialTail
