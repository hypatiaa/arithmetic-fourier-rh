import Verified
open MeasureTheory Filter Set
open scoped ContDiff
noncomputable section
namespace RHConnections.ParametricSignedSharp
open SpectralTail SmoothedPrimeLimit SmoothedPrimeSandwichUniform SharpChebyshevError PrimeRightCut ChebyshevCriterion
open SharpRadialTail (paramRightSum parametric_sharpened_zero_remainder)
open ParametricSharpRightEndpoint (width parametricShellRight)

def lowerMode (a T : ℝ) : ℂ :=
  parametricShellRight a T 1 (1+Real.log 2-width a T) (width a T)

def upperMode (a T : ℝ) : ℂ :=
  parametricShellRight a T (1-width a T) (1+Real.log 2) (width a T)

private theorem at_width {θ : ℝ} (hθ : 1/2≤θ) (hθ1 : θ<1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b T : ℝ}, 1 ≤ T → a ≤ b → 0 < a → b+width θ T < 3 →
    let f := fun x : ℝ => (shell a b (width θ T) x : ℂ)
    ‖(∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r)-paramRightSum θ T f‖ ≤
      C*Real.exp (-(1-θ)*T)*(T+2)^2 := by
  obtain ⟨A,B,hA,hB,hZ⟩ := parametric_sharpened_zero_remainder
  refine ⟨4*A+32*B,by positivity,?_⟩
  intro a b T hT hab ha hb
  let u := Real.exp (-(1-θ)*T)
  have hu : 0 < u := Real.exp_pos _
  have ht0 : 0 ≤ T := by linarith
  have he : 1 ≤ Real.exp (2*(1-θ)*T) := Real.one_le_exp (by positivity)
  obtain ⟨J,hl,hr⟩ := exists_nat_pow_near he (by norm_num : (1:ℝ)<2)
  have hlog : (1/2:ℝ) ≤ Real.log 2 := by
    have e := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at e
    norm_num at e
    linarith
  have hlogJ := Real.log_le_log (by positivity : (0:ℝ)<2^J) hl
  rw [Real.log_pow,Real.log_exp] at hlogJ
  have hcut : 2*(1-θ)*T≤T := by nlinarith only [mul_nonneg (show 0≤2*θ-1 by linarith) ht0]
  have hJ : (J:ℝ) ≤ 2*T := by nlinarith only [hcut,hlogJ,
    mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α:=ℝ) J)]
  have hpow : (0:ℝ)<2^J := by positivity
  have hhalf : (2^J:ℝ)⁻¹ ≤ 2*(u*u) := by
    have hrec := inv_anti₀ (Real.exp_pos _) hr.le
    have hinv : (Real.exp (2*(1-θ)*T))⁻¹ = u*u := by
      dsimp [u]; rw [← Real.exp_neg,← Real.exp_add]; congr 1; ring
    rw [hinv,pow_succ,_root_.mul_inv_rev] at hrec
    nlinarith
  have hz := hZ J hθ hθ1 hab (by dsimp [width]; positivity) ha hb ht0 hl hr.le
  apply hz.trans
  change A*u*((J:ℝ)+2)^2 + (B/(u/8))*((J:ℝ)+1)/2^J ≤ (4*A+32*B)*u*(T+2)^2
  have hJs : ((J:ℝ)+2)^2 ≤ 4*(T+2)^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0≤(J:ℝ)+2)
      (show (J:ℝ)+2≤2*(T+2) by linarith) 2
    nlinarith only [h]
  have hJ1 : (J:ℝ)+1 ≤ 2*(T+2)^2 := by nlinarith only [hJ,ht0,sq_nonneg T]
  have hHi : (B/(u/8))*((J:ℝ)+1)/2^J ≤ 16*B*u*((J:ℝ)+1) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ (B/(u/8))*((J:ℝ)+1))).trans_eq
    field_simp
    ring
  have hLo := mul_le_mul_of_nonneg_left hJs (mul_nonneg hA hu.le)
  have hHi' := hHi.trans (mul_le_mul_of_nonneg_left hJ1 (by positivity))
  nlinarith only [hLo,hHi']

private theorem prime_with_remainder {θ : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hf0 : ∀ x ≤ 0, f x=0) {T N : ℝ} (hT : 1 ≤ T)
    (hZ : ‖(∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r)-paramRightSum θ T f‖ ≤ N) :
    ‖Complex.exp (-(T:ℂ))*(∑' n : ℕ, mangoldtCoeff n * f (Real.log n-T)) -
      (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*f x) + paramRightSum θ T f‖ ≤
      ((2*∫ x : ℝ, ‖f x‖) + ‖∫ x in Ioi (0:ℝ), f x‖)*Real.exp (-T) + N := by
  have hT0 : 0 ≤ T := by linarith
  rw [smoothed_prime_explicit_identity hf hc hf0 hT0]
  let P := Complex.exp (-(T:ℂ)) * (∫ x in Ioi (0:ℝ), f x)
  let A := ∫ x in Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*scaleTest T f x
  let Z := ∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r
  have hP : ‖P‖ = ‖∫ x in Ioi (0:ℝ), f x‖*Real.exp (-T) := by
    simp only [P,norm_mul,Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,mul_comm]
  have hA := scaled_real_place_bound hf hc hf0 hT
  have h := (norm_sub_le (P-A) (Z-paramRightSum θ T f)).trans
    (add_le_add ((norm_sub_le P A).trans (add_le_add hP.le hA)) hZ)
  convert h using 1
  · congr 1
    dsimp only [P,A,Z]
    ring
  · ring
private theorem smooth_at_width {θ : ℝ} (hθ : 1/2≤θ) (hθ1 : θ<1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b T : ℝ}, 1 ≤ T → a ≤ b → 0 < a → b+width θ T < 3 →
    |realPrimeTest (shell a b (width θ T)) T - mass (shell a b (width θ T)) +
      (parametricShellRight θ T a b (width θ T)).re| ≤ C*Real.exp (-(1-θ)*T)*(T+2)^2 := by
  obtain ⟨C,hC,hZ⟩ := at_width hθ hθ1
  refine ⟨C+9,by positivity,?_⟩
  intro a b T hT hab ha hb
  let h := width θ T
  have hh : 0 < h := by dsimp [h,width]; positivity
  let f := shell a b h
  let g := fun x : ℝ => (f x:ℂ)
  have hs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp (shell_smooth a b h)
  have hz (x : ℝ) (hx : x ≤ 0) : g x = 0 := by simp [g,f,shell_left hab hh (hx.trans ha.le)]
  have gz (x : ℝ) (hx : x ∉ Ioc (0:ℝ) 3) : g x = 0 := by
    by_cases hx0 : x ≤ 0
    · exact hz x hx0
    · have hx3 : 3 < x := by by_contra! e; exact hx ⟨lt_of_not_ge hx0,e⟩
      simp [g,f,shell_right hab hh (hb.trans hx3).le]
  have hc : HasCompactSupport g := HasCompactSupport.intro (K := Icc (0:ℝ) 3) isCompact_Icc
    (fun x hx => gz x (fun e => hx ⟨e.1.le,e.2⟩))
  have hg1 (x : ℝ) : ‖g x‖ ≤ 1 := by
    have hf := shell_range hab hh x
    simpa [g,f,abs_of_nonneg hf.1] using hf.2
  have hi : (∫ x : ℝ, ‖g x‖) ≤ 3 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0:ℝ) 3)
      (f := fun x => ‖g x‖) (fun x hx => by simp [gz x hx])]
    calc
      _ ≤ ∫ _x in Ioc (0:ℝ) 3, (1:ℝ) := integral_mono
        (hs.continuous.integrable_of_hasCompactSupport hc).norm.integrableOn
        (integrableOn_const (measure_Ioc_lt_top.ne)) hg1
      _ = _ := by simp
  have hi2 : ‖∫ x in Ioi (0:ℝ), g x‖ ≤ 3 :=
    (norm_integral_le_integral_norm _).trans ((setIntegral_le_integral
      (hs.continuous.integrable_of_hasCompactSupport hc).norm (Eventually.of_forall fun _ => norm_nonneg _)).trans hi)
  have hshell := prime_with_remainder (θ := θ) hs hc hz hT (hZ hT hab ha hb)
  let D := Complex.exp (-(T:ℂ))*(∑' n : ℕ, mangoldtCoeff n * g (Real.log n-T)) -
    (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*g x)
  have hd : D = ((realPrimeTest f T-mass f:ℝ):ℂ) := by
    dsimp only [D,realPrimeTest,mass,g,mangoldtCoeff]
    simp only [←Complex.ofReal_neg,←Complex.ofReal_exp,←Complex.ofReal_mul,←Complex.ofReal_tsum,
      integral_complex_ofReal,←Complex.ofReal_sub]
  change |realPrimeTest f T-mass f+(paramRightSum θ T g).re|≤_
  rw [←Complex.ofReal_re (realPrimeTest f T-mass f),←hd,←Complex.add_re]
  refine (Complex.abs_re_le_norm (D+paramRightSum θ T g)).trans (hshell.trans ?_)
  have hbound : (2*∫ x : ℝ, ‖g x‖) + ‖∫ x in Ioi (0:ℝ), g x‖ ≤ 9 := by linarith
  have hex : Real.exp (-T) ≤ Real.exp (-(1-θ)*T) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg (show 0≤θ by linarith) (show 0≤T by linarith)])
  have hsquare : (1:ℝ) ≤ (T+2)^2 := by nlinarith [sq_nonneg T]
  have hx := le_mul_of_one_le_right (Real.exp_pos (-(1-θ)*T)).le hsquare
  linarith [mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-T)).le,hex.trans hx]

theorem parametric_signed_sharp_dyadic_log {θ : ℝ} (hθ : 1/2≤θ) (hθ1 : θ<1) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      let E := (Chebyshev.psi (2*Real.exp (T+1))-Chebyshev.psi (Real.exp (T+1)))-Real.exp (T+1);
      -(Real.exp T)*((lowerMode θ T).re+C*Real.exp (-(1-θ)*T)*(T+2)^2) ≤ E ∧
        E ≤ Real.exp T*(-(upperMode θ T).re+C*Real.exp (-(1-θ)*T)*(T+2)^2) := by
  obtain ⟨C,hC,hE⟩ := smooth_at_width hθ hθ1
  let q := 1+Real.log 2
  let M := 2*(Real.exp q + Real.exp 1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M/8+C,by positivity,?_⟩
  intro T hT
  let u := Real.exp (-(1-θ)*T)
  let h := width θ T
  have hu : 0 < u := Real.exp_pos _
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg (sub_nonneg.mpr hθ1.le) (show 0≤T by linarith)])
  have hh : 0 < h := by dsimp [h,width]; positivity
  have hh' : h = u/8 := rfl
  have hh1 : h ≤ 1/8 := by rw [hh']; linarith
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by
    have e := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at e
    norm_num at e
    linarith
  have hl' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hq : 1+h ≤ q-h := by dsimp [q]; linarith
  have hq' : q+h < 3 := by dsimp [q]; linarith
  have eqU : Real.exp (T+q) = 2*Real.exp (T+1) := by
    rw [show T+q=T+1+Real.log 2 by dsimp [q]; ring, Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm]
  have eqQ : Real.exp q = 2*Real.exp 1 := by
    rw [show q=1+Real.log 2 from rfl,Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm]
  have le1 := abs_le.mp (hE hT (by linarith : 1 ≤ q-h) (by norm_num)
    (by linarith) )
  have le2 := abs_le.mp (hE hT (by linarith : 1-h ≤ q) (by linarith)
    hq' )
  obtain ⟨ls,us⟩ := interval_sandwich hh hq T
  have m1 := (shell_mass hh (by norm_num : (0:ℝ)≤1) hq).1
  have m2 := (shell_mass hh (by linarith : 0 ≤ 1-h) (by linarith : 1-h+h≤q)).2
  have ep : Real.exp h-1 ≤ 2*h := (le_abs_self _).trans
    (by simpa [abs_of_pos hh] using Real.abs_exp_sub_one_le (x := h) (by rw [abs_of_pos hh]; linarith))
  have em := Real.add_one_le_exp (-h)
  rw [sub_eq_add_neg q h,Real.exp_add q (-h),Real.exp_add 1 h] at m1
  rw [sub_eq_add_neg (1:ℝ) h,Real.exp_add 1 (-h),Real.exp_add q h] at m2
  have h₁ := mul_le_mul_of_nonneg_left ep (Real.exp_pos 1).le
  have h₂ := mul_le_mul_of_nonneg_left ep (Real.exp_pos q).le
  have h₃ := mul_le_mul_of_nonneg_left em (Real.exp_pos 1).le
  have h₄ := mul_le_mul_of_nonneg_left em (Real.exp_pos q).le
  have h₅ := mul_nonneg hh.le (Real.exp_pos 1).le
  have h₆ := mul_nonneg hh.le (Real.exp_pos q).le
  have hsplit1 : (parametricShellRight θ T 1 (q-h) h).re=(lowerMode θ T).re := rfl
  have hsplit2 : (parametricShellRight θ T (1-h) q h).re=(upperMode θ T).re := rfl
  rw [hsplit1] at le1
  rw [hsplit2] at le2
  have hLower :
      -(lowerMode θ T).re-M*h-C*u*(T+2)^2 ≤ intervalShell 1 q T-(Real.exp q-Real.exp 1) := by
    dsimp only [M]
    rw [←sub_eq_add_neg] at m1
    linarith [le1.1]
  have hUpper :
      intervalShell 1 q T-(Real.exp q-Real.exp 1)≤-(upperMode θ T).re+M*h+C*u*(T+2)^2 := by
    dsimp only [M]
    rw [←sub_eq_add_neg] at m2
    linarith [le2.2]
  have hOne : (1:ℝ)≤(T+2)^2 := by nlinarith [sq_nonneg T]
  have hm := le_mul_of_one_le_right (mul_nonneg hM hu.le) hOne
  have hCompare : M*h≤(M/8)*u*(T+2)^2 := by
    rw [hh']
    nlinarith only [hm]
  have hid : Real.exp T*(intervalShell 1 q T-(Real.exp q-Real.exp 1)) =
      Chebyshev.psi (2*Real.exp (T+1)) - Chebyshev.psi (Real.exp (T+1)) - Real.exp (T+1) := by
    rw [intervalShell,eqU,eqQ,mul_sub,← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,
      Real.exp_add T 1]
    ring
  dsimp only
  rw [←hid]
  constructor
  · rw [neg_mul,←mul_neg]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos T).le
    linarith only [hLower,hCompare,show (M/8+C)*u*(T+2)^2=(M/8)*u*(T+2)^2+C*u*(T+2)^2 by ring]
  · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos T).le
    linarith only [hUpper,hCompare,show (M/8+C)*u*(T+2)^2=(M/8)*u*(T+2)^2+C*u*(T+2)^2 by ring]

end RHConnections.ParametricSignedSharp
