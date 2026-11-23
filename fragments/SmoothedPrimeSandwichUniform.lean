import Verified

open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section
namespace RHConnections.SmoothedPrimeSandwichUniform
open SmoothedPrimeLimit SpectralTail

abbrev step := Real.smoothTransition

def shell (a b h x : ℝ) : ℝ := step ((x-a)/h) - step ((x-b)/h)

theorem shell_smooth (a b h : ℝ) : ContDiff ℝ ∞ (shell a b h) := by
  apply ContDiff.sub <;> apply Real.smoothTransition.contDiff.comp <;> fun_prop

theorem shell_left {a b h x : ℝ} (hab : a ≤ b) (hh : 0 < h) (hx : x ≤ a) :
    shell a b h x = 0 := by
  unfold shell step
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le),
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le),sub_self]

theorem shell_right {a b h x : ℝ} (hab : a ≤ b) (hh : 0 < h) (hx : b+h ≤ x) :
    shell a b h x = 0 := by
  unfold shell step
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hh).2 (by linarith)),
      Real.smoothTransition.one_of_one_le ((le_div_iff₀ hh).2 (by linarith)),sub_self]

theorem shell_one {a b h x : ℝ} (hh : 0 < h) (hx : a+h ≤ x) (hy : x ≤ b) :
    shell a b h x = 1 := by
  unfold shell step
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hh).2 (by linarith)),
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le),sub_zero]

theorem shell_range {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) (x : ℝ) :
    0 ≤ shell a b h x ∧ shell a b h x ≤ 1 := by
  unfold shell step
  constructor
  · apply sub_nonneg.mpr
    apply Real.smoothTransition.monotone
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  · linarith [Real.smoothTransition.nonneg ((x-b)/h),Real.smoothTransition.le_one ((x-a)/h)]

theorem shell_compact {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) : HasCompactSupport (shell a b h) := by
  apply HasCompactSupport.intro (K := Icc a (b+h)) isCompact_Icc
  intro x hx
  by_cases hxa : x ≤ a
  · exact shell_left hab hh hxa
  · apply shell_right hab hh
    by_contra! h
    exact hx ⟨le_of_not_ge hxa,h.le⟩

theorem sandwich {h : ℝ} (hh : 0 < h) (ht : h ≤ 1/4) (x : ℝ) :
    shell 1 (2-h) h x ≤ (Ioc (1:ℝ) 2).indicator (fun _ => (1:ℝ)) x ∧
    (Ioc (1:ℝ) 2).indicator (fun _ => (1:ℝ)) x ≤ shell (1-h) 2 h x := by
  by_cases hx : x ∈ Ioc (1:ℝ) 2
  · rw [Set.indicator_of_mem hx,shell_one hh (by linarith [hx.1]) hx.2]
    exact ⟨(shell_range (by linarith : 1 ≤ 2-h) hh x).2,le_rfl⟩
  · rw [Set.indicator_of_notMem hx]
    refine ⟨?_,(shell_range (by linarith : 1-h ≤ 2) hh x).1⟩
    by_cases h1 : x ≤ 1
    · rw [shell_left (by linarith) hh h1]
    · rw [shell_right (by linarith) hh (by by_contra! e; exact hx ⟨lt_of_not_ge h1,by linarith⟩)]

private theorem step_smooth : ContDiff ℝ ∞ step := Real.smoothTransition.contDiff

private theorem step_deriv_compact : HasCompactSupport (deriv step) := by
  apply HasCompactSupport.intro (K := Icc (0:ℝ) 1) isCompact_Icc
  intro x hx
  by_cases h : x < 0
  · have he : step =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds h] with y hy using Real.smoothTransition.zero_of_nonpos hy.le
    simpa using he.deriv_eq
  · have h1 : 1 < x := by by_contra! e; exact hx ⟨le_of_not_gt h,e⟩
    have he : step =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
      filter_upwards [eventually_gt_nhds h1] with y hy using Real.smoothTransition.one_of_one_le hy.le
    simpa using he.deriv_eq

def curvature (a h x : ℝ) : ℝ := deriv (deriv step) ((x-a)/h) / h^2

def curvatureMass : ℝ := ∫ x : ℝ, ‖deriv (deriv step) x‖

theorem curvature_mass {h : ℝ} (hh : 0 < h) (a : ℝ) :
    (∫ x : ℝ, ‖curvature a h x‖) = curvatureMass/h := by
  simp only [curvature,norm_div,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg h)]
  rw [show (fun x : ℝ => |deriv (deriv step) ((x-a)/h)| / h^2) =
      fun x : ℝ => (fun y : ℝ => |deriv (deriv step) (h⁻¹*y)| / h^2) (x-a) by
        funext x; rw [div_eq_inv_mul (x-a) h],
      integral_sub_right_eq_self (fun y : ℝ => |deriv (deriv step) (h⁻¹*y)| / h^2) a,integral_div]
  have he := Measure.integral_comp_mul_left (fun x : ℝ => |deriv (deriv step) x|) h⁻¹
  simp only [inv_inv,abs_of_pos hh,smul_eq_mul] at he
  rw [he]
  unfold curvatureMass
  simp only [Real.norm_eq_abs]
  field_simp

theorem shell_curvature (a b h x : ℝ) :
    deriv (deriv (shell a b h)) x = curvature a h x - curvature b h x := by
  let A := fun c x : ℝ => (x-c)/h
  have hA (c y : ℝ) : HasDerivAt (A c) (1/h) y :=
    ((hasDerivAt_id y).sub_const c).div_const h
  have hd := step_smooth.differentiable (by simp)
  have hd' := (contDiff_infty_iff_deriv.mp step_smooth).2.differentiable (by simp)
  have hfirst : deriv (shell a b h) = fun y => deriv step (A a y)*(1/h) - deriv step (A b y)*(1/h) := by
    funext y
    exact (((hd _).hasDerivAt.comp y (hA a y)).sub ((hd _).hasDerivAt.comp y (hA b y))).deriv
  rw [hfirst]
  have he := ((((hd' _).hasDerivAt.comp x (hA a x)).mul_const (1/h)).sub
    (((hd' _).hasDerivAt.comp x (hA b x)).mul_const (1/h))).deriv
  convert he using 1 <;> first | rfl | (simp only [curvature,A,div_eq_mul_inv]; ring)

private theorem curvature_integrable {h : ℝ} (hh : 0 < h) (a : ℝ) : Integrable (curvature a h) := by
  have hs := (contDiff_infty_iff_deriv.mp step_smooth).2
  have hi : Integrable (deriv (deriv step)) := (hs.continuous_deriv (by simp)).integrable_of_hasCompactSupport step_deriv_compact.deriv
  have hg := ((integrable_comp_mul_left_iff _ (inv_ne_zero hh.ne')).2 hi).comp_sub_right a
  unfold curvature
  simpa only [div_eq_inv_mul (_ - a) h] using hg.div_const (h^2)

theorem shell_curvature_mass {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    (∫ x : ℝ, ‖deriv (deriv (shell a b h)) x‖) ≤ 2*curvatureMass/h := by
  simp_rw [shell_curvature]
  have h1 := curvature_integrable hh a
  have h2 := curvature_integrable hh b
  calc
    _ ≤ ∫ x : ℝ, (‖curvature a h x‖ + ‖curvature b h x‖) :=
      integral_mono (h1.sub h2).norm (h1.norm.add h2.norm) (fun x => norm_sub_le _ _)
    _ = _ := by rw [integral_add h1.norm h2.norm,curvature_mass hh,curvature_mass hh]; ring

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

theorem spectral_majorant {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h)
    (ha : 0 < a) (hb : b+h < 3) (r : NontrivialZetaZero) :
    ‖compactZeroTerm (scaleTest 0 (fun x => (shell a b h x : ℂ))) r‖ ≤
    ((analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2) *
      (Real.exp 3 * (2*curvatureMass) / h) := by
  let f := shell a b h
  let z := r.val
  let E := fun x : ℝ => Complex.exp (z*(x:ℂ))
  have hs : ContDiff ℝ ∞ f := shell_smooth _ _ _
  have hs' := (contDiff_infty_iff_deriv.mp hs).2
  have hs'' := (contDiff_infty_iff_deriv.mp hs').2
  have hd := hs.differentiable (by simp)
  have hd' := hs'.differentiable (by simp)
  have h0 : f =ᶠ[𝓝 (0:ℝ)] (fun _ => 0) := by
    filter_upwards [eventually_lt_nhds ha] with x hx using shell_left hab hh hx.le
  have h3 : f =ᶠ[𝓝 (3:ℝ)] (fun _ => 0) := by
    filter_upwards [eventually_gt_nhds hb] with x hx using shell_right hab hh hx.le
  have h1 := transfer z (fun x => (hd x).hasDerivAt.ofReal_comp)
    (Complex.continuous_ofReal.comp hs'.continuous) (by simp [h0.eq_of_nhds])
    (by simp [h3.eq_of_nhds])
  have h2 := transfer z (fun x => (hd' x).hasDerivAt.ofReal_comp)
    (Complex.continuous_ofReal.comp hs''.continuous) (by simp [h0.deriv_eq])
    (by simp [h3.deriv_eq])
  have hid : z^2 * (∫ x in (0:ℝ)..3, E x*(f x:ℂ)) =
      ∫ x in (0:ℝ)..3, E x*((deriv (deriv f) x : ℝ):ℂ) := by
    dsimp [E]
    linear_combination z * h1 - h2
  have hfI : Integrable (fun x => ‖deriv (deriv f) x‖) :=
    (hs''.continuous.integrable_of_hasCompactSupport (shell_compact hab hh).deriv.deriv).norm
  have hei (x : ℝ) (hx : x ∈ Icc (0:ℝ) 3) : ‖E x‖ ≤ Real.exp 3 := by
    rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right r.property.1.2.le hx.1).trans (by simpa using hx.2)
  have hnorm : ‖∫ x in (0:ℝ)..3, E x*((deriv (deriv f) x : ℝ):ℂ)‖ ≤
      Real.exp 3 * (2*curvatureMass/h) := by
    have hEc : Continuous E := by unfold E; fun_prop
    calc
      _ ≤ ∫ x in (0:ℝ)..3, ‖E x*((deriv (deriv f) x : ℝ):ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ x in (0:ℝ)..3, Real.exp 3 * ‖deriv (deriv f) x‖ := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((hEc.mul (Complex.continuous_ofReal.comp hs''.continuous)).norm.intervalIntegrable _ _)
          ((continuous_const.mul hs''.continuous.norm).intervalIntegrable _ _)
        intro x hx
        simp only [Pi.mul_apply,Function.comp_apply,norm_mul,Complex.norm_real]
        exact mul_le_mul_of_nonneg_right (hei x hx) (norm_nonneg _)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3)]
        exact mul_le_mul_of_nonneg_left ((setIntegral_le_integral hfI
          (Filter.Eventually.of_forall fun x => norm_nonneg _)).trans (shell_curvature_mass hh a b)) (Real.exp_pos _).le
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
  have hv := congrArg norm hid
  rw [norm_mul,norm_pow] at hv
  have hB := (le_div_iff₀ (sq_pos_of_pos hn)).2 (by simpa only [mul_comm _ (‖z‖^2)] using hv.le.trans hnorm)
  calc
    _ ≤ (analyticOrderNatAt riemannZeta r.val:ℝ) * ((Real.exp 3 * (2*curvatureMass/h))/‖z‖^2) :=
      mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
    _ = _ := by unfold z; ring

end RHConnections.SmoothedPrimeSandwichUniform
