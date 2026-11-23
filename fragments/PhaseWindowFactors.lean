import Verified
import PhaseWindow

noncomputable section
namespace RHConnections.PhaseWindow

def oppositeOffset (freq : ℂ) : ℝ := Real.pi / |freq.im|

def oppositeShift (freq : ℂ) : Shift :=
  ⟨((1+Real.exp (freq.re*oppositeOffset freq))⁻¹:ℝ), oppositeOffset freq⟩

theorem opposite_offset_positive {freq : ℂ} (hf : freq.im≠0) :
    0<oppositeOffset freq := div_pos Real.pi_pos (abs_pos.mpr hf)

theorem opposite_exponential {freq : ℂ} (hf : freq.im≠0) :
    Complex.exp (freq*(oppositeOffset freq:ℂ)) =
      -(Real.exp (freq.re*oppositeOffset freq):ℂ) := by
  let h := oppositeOffset freq
  have he : freq*(h:ℂ) = ((freq.re*h:ℝ):ℂ)+((freq.im*h:ℝ):ℂ)*Complex.I := by
    conv_lhs => rw [←Complex.re_add_im freq]
    push_cast
    ring

  have him : Complex.exp (((freq.im*h:ℝ):ℂ)*Complex.I) = -1 := by
    rcases lt_or_gt_of_ne hf with hn | hp
    · have hh : freq.im*h = -Real.pi := by
        dsimp [h,oppositeOffset]; rw [abs_of_neg hn]; field_simp
      rw [hh,Complex.ofReal_neg,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
      norm_num
    · have hh : freq.im*h = Real.pi := by
        dsimp [h,oppositeOffset]; rw [abs_of_pos hp]; field_simp
      rw [hh,Complex.exp_pi_mul_I]
  change Complex.exp (freq*(h:ℂ)) = _
  rw [he,Complex.exp_add,him,←Complex.ofReal_exp]
  ring

theorem opposite_shift_kills {freq : ℂ} (hf : freq.im≠0) :
    shiftFactor freq (oppositeShift freq) = 0 := by
  rw [shiftFactor]
  simp only [oppositeShift]
  rw [opposite_exponential hf]
  let e := Real.exp (freq.re*oppositeOffset freq)
  change 1-(((1+e)⁻¹:ℝ):ℂ)+(((1+e)⁻¹:ℝ):ℂ)*(-(e:ℂ))=0
  have he : (1+e:ℝ)≠0 := by positivity
  exact_mod_cast (show 1-(1+e)⁻¹+(1+e)⁻¹*(-e)=0 by field_simp [he]; ring)

theorem opposite_shift_cost (freq : ℂ) :
    ‖1-(oppositeShift freq).weight‖+‖(oppositeShift freq).weight‖=1 := by
  let e := Real.exp (freq.re*oppositeOffset freq)
  have hw : 0≤(1+e)⁻¹ := by positivity
  have hw1 : (1+e)⁻¹≤1 := inv_le_one_of_one_le₀ (by linarith [Real.exp_pos (freq.re*oppositeOffset freq)])
  change ‖1-(((1+e)⁻¹:ℝ):ℂ)‖+‖(((1+e)⁻¹:ℝ):ℂ)‖=1
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hw,abs_of_nonneg (sub_nonneg.mpr hw1)]
  ring

def signedShift (freq : ℂ) (h : ℝ) : Shift :=
  ⟨(1-Complex.exp (freq*(h:ℂ)))⁻¹,h⟩

theorem signed_shift_kills (freq : ℂ) (h : ℝ) (he : Complex.exp (freq*(h:ℂ))≠1) :
    shiftFactor freq (signedShift freq h)=0 := by
  dsimp [shiftFactor,signedShift]
  field_simp [sub_ne_zero.mpr he.symm]
  <;> ring

theorem exists_signed_shift {freq : ℂ} (hf : freq≠0) {η : ℝ} (hη : 0<η) :
    ∃ e : Shift, 0<e.offset ∧ e.offset≤η ∧ shiftFactor freq e=0 := by
  let h := min η (Real.pi/(1+|freq.im|))
  have hh : 0<h := lt_min hη (by positivity [Real.pi_pos])
  have him : |freq.im*h| < 2*Real.pi := by
    rw [abs_mul,abs_of_pos hh]
    have hA : |freq.im| *(Real.pi/(1+|freq.im|)) < Real.pi := by
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [Real.pi_pos]
    exact ((mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg _)).trans_lt hA).trans
      (by linarith [Real.pi_pos])
  have he : Complex.exp (freq*(h:ℂ))≠1 := by
    intro he
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp he
    have hik := congrArg Complex.im hk
    simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,Complex.intCast_re,
      Complex.intCast_im,zero_mul,mul_zero,zero_add,add_zero,Complex.I_im,Complex.I_re]
      at hik
    have hik2 : freq.im*h=(k:ℝ)*(2*Real.pi) := by
      simpa [Complex.mul_im,Complex.ofReal_re] using hik
    rw [hik2,abs_mul,abs_of_pos (by positivity [Real.pi_pos] : 0<2*Real.pi)] at him
    have hkabs : |(k:ℝ)|<1 := by
      by_contra! hle
      have hm := mul_le_mul_of_nonneg_right hle (by positivity [Real.pi_pos] : 0≤2*Real.pi)
      rw [one_mul] at hm
      exact (not_lt_of_ge hm) him
    have hk0 : k=0 := by
      have hkI : |k|<1 := by exact_mod_cast hkabs
      have := abs_lt.mp hkI
      omega
    simp only [hk0,Int.cast_zero,zero_mul] at hk
    exact (mul_ne_zero hf (Complex.ofReal_ne_zero.mpr hh.ne')) hk
  exact ⟨signedShift freq h,hh,min_le_left _ _,signed_shift_kills freq h he⟩

end RHConnections.PhaseWindow
