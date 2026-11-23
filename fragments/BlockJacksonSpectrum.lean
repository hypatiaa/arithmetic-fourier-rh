import Verified
import Mathlib.Analysis.Fourier.ZMod

open AddChar
noncomputable section
namespace RHConnections.BlockFourier

variable {J : ℕ} [NeZero J]

def tone (k x : ZMod J) : ℂ := ZMod.stdAddChar (k*x)

private theorem tone_add (a b x : ZMod J) : tone (a+b) x = tone a x*tone b x := by
  rw [tone,add_mul,map_add_eq_mul]
  rfl

theorem tone_shift (k a h : ZMod J) : tone k (a+h) = tone k a*tone k h := by
  rw [tone,mul_add,map_add_eq_mul]
  rfl

private theorem tone_conj (k x : ZMod J) : (starRingEnd ℂ) (tone k x) = tone (-k) x := by
  simp only [tone,neg_mul,map_neg_eq_conj]

private theorem dft_tone (l k : ZMod J) :
    ZMod.dft (tone l) k = if l=k then (J:ℂ) else 0 := by
  rw [ZMod.dft_apply]
  simp only [tone,smul_eq_mul,← map_add_eq_mul]
  have he (x : ZMod J) : -(x*k)+l*x = (l-k)*x := by ring
  simp only [he]
  by_cases h : l=k
  · subst l
    simp [ZMod.card]
  · rw [ite_eq_right h]
    exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar J (sub_ne_zero.mpr h))

def initialCharacterSum (R : ℕ) (x : ZMod J) : ℂ :=
  ∑ a ∈ Finset.range R,tone (a:ZMod J) x

def fourthWeight (R : ℕ) (x : ZMod J) : ℝ := ‖initialCharacterSum R x‖^4

def normalizingMass (R : ℕ) : ℝ := ∑ x : ZMod J, fourthWeight R x

def smoothingKernel (R : ℕ) (x : ZMod J) : ℝ :=
  fourthWeight R x / normalizingMass (J := J) R

theorem normalizing_mass_positive {R : ℕ} (hR : 0<R) : 0 < normalizingMass (J := J) R := by
  have he : initialCharacterSum R (0:ZMod J) = (R:ℂ) := by
    simp [initialCharacterSum,tone]
  have hpos : 0 < fourthWeight R (0:ZMod J) := by
    rw [fourthWeight,he,Complex.norm_natCast]
    positivity
  exact hpos.trans_le (Finset.single_le_sum (fun x _ => show 0≤fourthWeight R x by
    unfold fourthWeight; positivity) (Finset.mem_univ (0:ZMod J)))

theorem smoothing_kernel_nonneg (R : ℕ) (x : ZMod J) : 0 ≤ smoothingKernel R x := by
  exact div_nonneg (by unfold fourthWeight; positivity)
    (Finset.sum_nonneg (fun x _ => show 0≤fourthWeight R x by unfold fourthWeight; positivity))

theorem smoothing_kernel_mass {R : ℕ} (hR : 0<R) :
    (∑ x : ZMod J, smoothingKernel R x) = 1 := by
  unfold smoothingKernel
  rw [← Finset.sum_div]
  exact div_self (normalizing_mass_positive (J := J) hR).ne'

theorem fourth_weight_expansion (R : ℕ) (x : ZMod J) :
    (fourthWeight R x:ℂ) =
      ∑ a ∈ Finset.range R, ∑ b ∈ Finset.range R, ∑ c ∈ Finset.range R, ∑ d ∈ Finset.range R,
        tone ((((d:ℤ)+(c:ℤ)-(b:ℤ)-(a:ℤ)):ℤ):ZMod J) x := by
  let D := initialCharacterSum R x
  let E := ∑ a ∈ Finset.range R,tone (-(a:ZMod J)) x
  have hconj : (starRingEnd ℂ) D=E := by
    simp only [D,E,initialCharacterSum,map_sum,tone_conj]
  have habs : (fourthWeight R x:ℂ)=D*D*E*E := by
    change ((‖D‖^4:ℝ):ℂ)=_
    rw [← hconj]
    calc
      _ = ((‖D‖^2:ℝ):ℂ)^2 := by push_cast; ring
      _ = _ := by rw [Complex.sq_norm,← Complex.mul_conj]; ring
  rw [habs]
  unfold D E initialCharacterSum
  simp only [Finset.sum_mul,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  simp only [sub_eq_add_neg,Int.cast_add,Int.cast_natCast,Int.cast_neg,tone_add]

def lowBand (R : ℕ) (k : ZMod J) : Prop :=
  ∃ m : ℤ, -(2*(R:ℤ)-2) ≤ m ∧ m ≤ 2*(R:ℤ)-2 ∧ (m:ZMod J)=k

theorem fourth_weight_dft_zero (R : ℕ) {k : ZMod J} (hk : ¬lowBand R k) :
    ZMod.dft (fun x => (fourthWeight R x:ℂ)) k=0 := by
  rw [show (fun x : ZMod J => (fourthWeight R x:ℂ)) =
      ∑ a ∈ Finset.range R, ∑ b ∈ Finset.range R, ∑ c ∈ Finset.range R, ∑ d ∈ Finset.range R,
        tone ((((d:ℤ)+(c:ℤ)-(b:ℤ)-(a:ℤ)):ℤ):ZMod J) from by
    ext x; simpa only [Finset.sum_apply] using fourth_weight_expansion R x]
  simp only [map_sum,Finset.sum_apply,dft_tone]
  refine Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun b hb =>
    Finset.sum_eq_zero (fun c hc => Finset.sum_eq_zero (fun d hd => ?_))))
  have hne : (((d:ℤ)+(c:ℤ)-(b:ℤ)-(a:ℤ):ℤ):ZMod J)≠k := by
    intro hh
    have haa := Finset.mem_range.mp ha
    have hbb := Finset.mem_range.mp hb
    have hcc := Finset.mem_range.mp hc
    have hdd := Finset.mem_range.mp hd
    exact hk ⟨_,by omega,by omega,hh⟩
  simp only [ite_eq_right hne]

theorem smoothing_kernel_dft_zero (R : ℕ) {k : ZMod J} (hk : ¬lowBand R k) :
    ZMod.dft (fun x => (smoothingKernel R x:ℂ)) k=0 := by
  have he : (fun x : ZMod J => (smoothingKernel R x:ℂ)) =
      (fun x : ZMod J => (fourthWeight R x:ℂ)*((normalizingMass (J := J) R:ℝ):ℂ)⁻¹) := by
    ext x; simp [smoothingKernel,div_eq_mul_inv]
  rw [he,ZMod.dft_mul_const]
  dsimp only
  rw [fourth_weight_dft_zero R hk,zero_mul]

def cyclicConvolution (f d : ZMod J → ℂ) (x : ZMod J) : ℂ :=
  ∑ h : ZMod J,f h*d (x-h)

theorem cyclic_convolution_dft (f d : ZMod J → ℂ) (k : ZMod J) :
    ZMod.dft (cyclicConvolution f d) k = ZMod.dft f k * ZMod.dft d k := by
  simp only [ZMod.dft_apply,cyclicConvolution,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  exact Fintype.sum_equiv (Equiv.subRight h) (fun x => ZMod.stdAddChar (-(x*k))*(f h*d (x-h)))
    (fun y => (ZMod.stdAddChar (-(h*k))*f h)*(ZMod.stdAddChar (-(y*k))*d y)) (fun x => by
      change ZMod.stdAddChar (-(x*k))*(f h*d (x-h)) =
        (ZMod.stdAddChar (-(h*k))*f h)*(ZMod.stdAddChar (-((x-h)*k))*d (x-h))
      have he : -(x*k) = -(h*k)+-((x-h)*k) := by ring
      rw [he,map_add_eq_mul]
      ring)

theorem low_pass_support (R : ℕ) (d : ZMod J → ℂ) {k : ZMod J} (hk : ¬lowBand R k) :
    ZMod.dft (cyclicConvolution (fun h => (smoothingKernel R h:ℂ)) d) k=0 := by
  rw [cyclic_convolution_dft,smoothing_kernel_dft_zero R hk,zero_mul]

theorem smoothing_kernel_even (R : ℕ) (h : ZMod J) :
    smoothingKernel R (-h)=smoothingKernel R h := by
  have he : initialCharacterSum R (-h) = (starRingEnd ℂ) (initialCharacterSum R h) := by
    simp only [initialCharacterSum,tone,mul_neg,map_neg_eq_conj,map_sum]
  simp only [smoothingKernel,fourthWeight,he,Complex.norm_conj]

def smoothReal (R : ℕ) (d : ZMod J → ℝ) (x : ZMod J) : ℝ :=
  ∑ h : ZMod J, smoothingKernel R h*d (x+h)

theorem complexification_of_real_smoothing (R : ℕ) (d : ZMod J → ℝ) :
    (fun x => (smoothReal R d x:ℂ)) =
      cyclicConvolution (fun h => (smoothingKernel R h:ℂ)) (fun x => (d x:ℂ)) := by
  ext1 x
  simp only [smoothReal,Complex.ofReal_sum,Complex.ofReal_mul,cyclicConvolution]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun h => ?_)
  change (smoothingKernel R h:ℂ)*(d (x+h):ℂ) =
    (smoothingKernel R (-h):ℂ)*(d (x-(-h)):ℂ)
  rw [smoothing_kernel_even,sub_neg_eq_add]

theorem real_smoothing_low_pass_support (R : ℕ) (d : ZMod J → ℝ) {k : ZMod J}
    (hk : ¬lowBand R k) :
    ZMod.dft (fun x => (smoothReal R d x:ℂ)) k=0 := by
  rw [complexification_of_real_smoothing]
  exact low_pass_support R _ hk

end RHConnections.BlockFourier
