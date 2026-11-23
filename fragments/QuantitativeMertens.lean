import Verified
import FinitePerronMertens
import ReciprocalEulerDisk

noncomputable section
open Set Complex
namespace RHConnections.FinitePerron
open PerronRamp ZetaDiskLog ZetaZeroFreeRegion PoleCompensation MertensCriterion
open ReciprocalLocalComparison

private theorem finite_height_factor (a v t : ℝ) (ha : 0≤a) (ha1 : a≤1)
    (hv : 1≤v) (ht : |t|≤Real.exp (a*v)) : heightFactor t ≤ 6*v := by
  have he : 1 ≤ Real.exp (a*v) := Real.one_le_exp_iff.mpr (by positivity)
  have harg : 3+2*|t| ≤ 5*Real.exp (a*v) := by linarith
  have hlog := Real.log_le_log (by positivity : 0<3+2*|t|) harg
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp] at hlog
  have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)
  unfold heightFactor
  nlinarith only [hlog,h5,hv,mul_le_mul_of_nonneg_right ha1 (by linarith : 0≤v)]

private theorem reg_nonzero_of_exclusion {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1/2)
    (hexcl : ∀ r : SpectralTail.NontrivialZetaZero,
      r.val.re≤1-κ/heightFactor r.val.im) {s : ℂ}
    (hs : 1-κ/heightFactor s.im<s.re) : regularizedZeta s≠0 := by
  by_cases h1 : s=1
  · rw [h1,regularizedZeta_one]
    exact one_ne_zero
  rw [(regularizedZeta_germ h1).eq_of_nhds]
  apply mul_ne_zero (sub_ne_zero.mpr h1)
  intro hz
  have hsr : s.re<1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
  have hb := (div_le_self hκ.le (heightFactor_one_le s.im)).trans hκ1
  let r : SpectralTail.NontrivialZetaZero := ⟨s,⟨by linarith,hsr⟩,hz⟩
  exact not_le_of_gt hs (hexcl r)

theorem quantitative_mertens_of_log_reciprocal
    (d D : ℝ) (hd : 0<d) (hD : 0≤D)
    (hRecip : ∀ s : ℂ, 1-d/heightFactor s.im ≤ s.re → s.re≤2 →
      ‖zetaReciprocal s‖≤D*(1+|s.im|)^(1/4:ℝ)) :
    ∃ α C : ℝ, 0<α ∧ 0≤C ∧ ∀ X : ℝ, Real.exp 1≤X →
      ‖mertens X‖≤C*X*Real.exp (-α*Real.sqrt (Real.log X)) := by
  obtain ⟨κ,hκ,hκ1,hκzero⟩ := all_height_logarithmic_exclusion
  let m := min (d/6) (κ/12)
  have hm : 0<m := lt_min (by positivity) (by positivity)
  have hmκ : m≤κ/12 := min_le_right _ _
  have hmd : m≤d/6 := min_le_left _ _
  have hm1 : m≤1/4 := by linarith
  let a := m/16
  have ha : 0<a := by dsimp [a]; positivity
  have ha1 : a≤1 := by dsimp [a]; linarith
  let P := 2+2/(a/4)^2
  let C := 6+(|2*Real.pi|)⁻¹*
    (8*D*(2+Real.exp 3)+8*D*Real.exp 1*Real.exp 3+2*P*Real.exp 1*Real.exp 3)
  refine ⟨a/4,C,by positivity,by dsimp [C,P]; positivity,?_⟩
  intro X hX
  have hX1 : 1≤X := (Real.one_le_exp_iff.mpr zero_le_one).trans hX
  have hXp : 0<X := zero_lt_one.trans_le hX1
  have hlog : 1≤Real.log X := by
    have he := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at he
  let v := Real.sqrt (Real.log X)
  have hv : 1≤v := by simpa [v] using Real.sqrt_le_sqrt hlog
  have hv0 : 0<v := zero_lt_one.trans_le hv
  have hv2 : v^2=Real.log X := Real.sq_sqrt (by linarith)
  have hv21 : 1≤v^2 := by nlinarith
  let b := 1-m/v
  let c := 1+1/v^2
  let T := Real.exp (a*v)
  let h := Real.exp (-(a*v/2))
  let U := 2*D*Real.exp (a*v/4)
  let W := 2+v^2
  let E := Real.exp (-(a/4)*v)
  have hb : 1/2≤b := by
    dsimp [b]
    linarith [div_le_self hm.le hv]
  have hb1 : b≤1 := sub_le_self _ (by positivity)
  have hc : 1<c := by dsimp [c]; linarith [show 0<1/v^2 by positivity]
  have hc2 : c≤2 := by dsimp [c]; linarith [div_le_self (show (0:ℝ)≤1 by norm_num) hv21]
  have hbc : b≤c := hb1.trans hc.le
  have hh : 0<h := Real.exp_pos _
  have hh1 : h≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hT : 0<T := Real.exp_pos _
  have hreg (s : ℂ) (hsr : s.re ∈ Icc b c) (hsi : s.im ∈ Icc (-T) T) :
      regularizedZeta s≠0 := by
    have hH := finite_height_factor a v s.im ha.le ha1 hv (abs_le.mpr hsi)
    have hH0 := (heightFactor_one_le s.im).trans_lt' zero_lt_one
    have hineq : m/v < κ/heightFactor s.im := by
      rw [div_lt_div_iff₀ hv0 hH0]
      have h₁ := mul_le_mul_of_nonneg_left hH hm.le
      have h₂ := mul_le_mul_of_nonneg_right hmκ hv0.le
      nlinarith only [h₁,h₂,mul_pos hκ hv0]
    exact reg_nonzero_of_exclusion hκ hκ1 (fun r => (hκzero r).2)
      ((sub_lt_sub_left hineq 1).trans_le hsr.1)
  have hUni (s : ℂ) (hsr : s.re ∈ Icc b c) (hsi : |s.im|≤T) :
      ‖zetaReciprocal s‖≤U := by
    have hH := finite_height_factor a v s.im ha.le ha1 hv hsi
    have hH0 := (heightFactor_one_le s.im).trans_lt' zero_lt_one
    have hineq : m/v ≤ d/heightFactor s.im := by
      rw [div_le_div_iff₀ hv0 hH0]
      have h₁ := mul_le_mul_of_nonneg_left hH hm.le
      have h₂ := mul_le_mul_of_nonneg_right hmd hv0.le
      nlinarith only [h₁,h₂]
    have he := hRecip s ((sub_le_sub_left hineq 1).trans hsr.1) (hsr.2.trans hc2)
    have hTp : 1≤T := Real.one_le_exp_iff.mpr (by positivity)
    have hel : 1+|s.im|≤2*T := by linarith
    have hpow : (1+|s.im|)^(1/4:ℝ)≤2*Real.exp (a*v/4) := by
      refine (Real.rpow_le_rpow (by positivity) hel (by norm_num)).trans ?_
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hT.le]
      have h₂ : (2:ℝ)^(1/4:ℝ)≤2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (1/4:ℝ)≤1)
      rw [show T^(1/4:ℝ)=Real.exp (a*v/4) by
        dsimp [T]; rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]; ring_nf]
      gcongr
    exact he.trans ((mul_le_mul_of_nonneg_left hpow hD).trans_eq (by dsimp [U]; ring))
  have hvRe (x t : ℝ) : (PerronRampBounds.vertical x t).re = x := by
    simp [PerronRampBounds.vertical,Complex.mul_re]
  have hvIm (x t : ℝ) : (PerronRampBounds.vertical x t).im = t := by
    simp [PerronRampBounds.vertical,Complex.mul_im]
  have heuler (t : ℝ) : ‖zetaReciprocal (PerronRampBounds.vertical c t)‖ ≤ W := by
    have he := euler_reciprocal_bound (s := PerronRampBounds.vertical c t) (by rwa [hvRe])
    rw [hvRe] at he
    have hec : c-1=1/v^2 := by dsimp [c]; ring
    rwa [hec,one_div_div,div_one] at he
  have hmain := finite_perron_mertens_bound hX1 hh hh1 hb hbc hc (hc2.trans (by norm_num))
    hT (show 0≤U by dsimp [U]; positivity) (show 0≤U by dsimp [U]; positivity)
    (show 0≤W by dsimp [W]; positivity) hreg
    (fun t ht => hUni _ (by simpa only [hvRe] using (show b∈Icc b c from ⟨le_rfl,hbc⟩))
      (by simpa only [hvIm] using abs_le.mpr ht))
    (fun x hx t ht => hUni _ (by simpa only [hvRe] using hx) (by rw [hvIm,ht]))
    heuler

  have hXb : X^b=X*Real.exp (-m*v) := by
    rw [Real.rpow_def_of_pos hXp,←hv2]
    have hp : v^2*b=v^2 + -m*v := by dsimp [b]; field_simp; ring
    rw [hp,Real.exp_add,hv2,Real.exp_log hXp]
  have hXc : X^c=X*Real.exp 1 := by
    rw [Real.rpow_def_of_pos hXp,←hv2]
    have hp : v^2*c=v^2 + 1 := by dsimp [c]; field_simp <;> ring
    rw [hp,Real.exp_add,hv2,Real.exp_log hXp]
  have hScale : 1≤X*E := by
    rw [show X=Real.exp (v^2) by rw [hv2,Real.exp_log hXp],show E=Real.exp (-(a/4)*v) by rfl,←Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have hpos : 0≤v*(v-a/4) := mul_nonneg hv0.le (by linarith)
    nlinarith only [hpos]
  have hsmall : h≤E := Real.exp_le_exp.mpr (by nlinarith [mul_pos ha hv0])
  have hsmooth : 3*(X*h+1)≤6*(X*E) := by linarith [mul_le_mul_of_nonneg_left hsmall hXp.le]
  have hVert : 4*T*U*X^b*(2+Real.exp 3) ≤
      8*D*(2+Real.exp 3)*(X*E) := by
    rw [hXb]
    have H : Real.exp (a*v)*Real.exp (a*v/4)*Real.exp (-m*v) ≤ E := by
      rw [←Real.exp_add,←Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [a,E]
      nlinarith [mul_pos hm hv0]
    calc
      _ = (8*D*(2+Real.exp 3)*X)*(Real.exp (a*v)*Real.exp (a*v/4)*Real.exp (-m*v)) := by dsimp [T,U]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left H (by positivity)).trans_eq (by ring)
  have hInvHoriz : Real.exp (a*v/4)/(h*T^2)≤E := by
    dsimp [T,h]
    rw [← Real.exp_nat_mul,←Real.exp_add,←Real.exp_sub]
    apply Real.exp_le_exp.mpr
    dsimp [E]
    nlinarith [mul_pos ha hv0]
  have hWidth : c-b≤2 := by linarith
  have hHoriz : 2*(c-b)*U*X^c*Real.exp 3/(h*T^2) ≤
      8*D*Real.exp 1*Real.exp 3*(X*E) := by
    rw [hXc]
    calc
      _ = (4*D*X*Real.exp 1*Real.exp 3)*((c-b)*(Real.exp (a*v/4)/(h*T^2))) := by dsimp [U]; ring
      _ ≤ (4*D*X*Real.exp 1*Real.exp 3)*(2*E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hWidth hInvHoriz (by positivity) (by norm_num)) (by positivity)
      _ = _ := by ring
  have hWexp : W≤P*Real.exp ((a/4)*v) := by
    let y := (a/4)*v
    have hy : 0≤y := by dsimp [y]; positivity
    have hh := Real.pow_div_factorial_le_exp y hy 2
    norm_num at hh
    have hWv : v^2≤(2/(a/4)^2)*Real.exp y := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0<(a/4)^2)).mpr
      dsimp [y] at hh
      nlinarith only [hh,show v^2*(a/4)^2=((a/4)*v)^2 by ring]
    dsimp only [W,P,y] at *
    rw [add_mul]
    linarith only [hWv,Real.one_le_exp_iff.mpr hy]
  have hWtail : W/(h*T)≤P*E := by
    calc
      _ ≤ (P*Real.exp ((a/4)*v))/(h*T) := div_le_div_of_nonneg_right hWexp (by positivity)
      _ = _ := by
        dsimp [h,T,E]
        rw [mul_div_assoc,←Real.exp_add,←Real.exp_sub]
        congr 1
        ring_nf
  have hRight : 2*W*X^c*Real.exp 3/(h*T) ≤
      2*P*Real.exp 1*Real.exp 3*(X*E) := by
    rw [hXc]
    calc
      _ = (2*X*Real.exp 1*Real.exp 3)*(W/(h*T)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hWtail (by positivity)).trans_eq (by ring)
  exact hmain.trans ((add_le_add hsmooth (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hVert hHoriz) hRight) (by positivity))).trans_eq (by dsimp [C,E]; ring))

end RHConnections.FinitePerron
