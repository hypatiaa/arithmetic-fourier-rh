import Verified

noncomputable section
namespace RHConnections.BlockFourier
open RHConnections.RankPairing
variable {J : ℕ} [NeZero J]

def complexIntervalSum (d : ZMod J → ℂ) (a : ZMod J) (len : ℕ) : ℂ :=
  ∑ i∈Finset.range len, d (a+(i:ZMod J))

def smoothComplexPositive (L : ZMod J → ℝ) (d : ZMod J → ℂ) (x : ZMod J) : ℂ :=
  ∑ h : ZMod J, (L h:ℂ)*d (x+h)

theorem complex_interval_smoothing_bound (d : ZMod J → ℂ) (L : ZMod J → ℝ)
    (H : ℝ) (hH : ∀ x, ‖d x‖≤H) (hL : ∑ h,L h=1)
    (a : ZMod J) (len : ℕ) :
    ‖complexIntervalSum (d-smoothComplexPositive L d) a len‖ ≤
      4*H*(∑ h,|L h| * (blockCyclicDistance h:ℝ)) := by
  have heRe : (complexIntervalSum (d-smoothComplexPositive L d) a len).re =
      blockIntervalSum (fun x => (d x).re-∑ h,L h*(d (x+h)).re) a len := by
    change Complex.reCLM (complexIntervalSum (d-smoothComplexPositive L d) a len) = _
    simp only [complexIntervalSum,blockIntervalSum,smoothComplexPositive,Pi.sub_apply,map_sum,
      map_sub,Complex.reCLM_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

  have heIm : (complexIntervalSum (d-smoothComplexPositive L d) a len).im =
      blockIntervalSum (fun x => (d x).im-∑ h,L h*(d (x+h)).im) a len := by
    change Complex.imCLM (complexIntervalSum (d-smoothComplexPositive L d) a len) = _
    simp only [complexIntervalSum,blockIntervalSum,smoothComplexPositive,Pi.sub_apply,map_sum,
      map_sub,Complex.imCLM_apply,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

  have hre := block_interval_smoothing (fun x => (d x).re) L H
    (fun x => (Complex.abs_re_le_norm _).trans (hH x)) hL a len
  have him := block_interval_smoothing (fun x => (d x).im) L H
    (fun x => (Complex.abs_im_le_norm _).trans (hH x)) hL a len
  exact (Complex.norm_le_abs_re_add_abs_im _).trans
    ((add_le_add (by simpa only [heRe] using hre) (by simpa only [heIm] using him)).trans_eq (by ring))

theorem complex_interval_jackson_bound (d : ZMod J → ℂ)
    (H : ℝ) (hH : ∀ x, ‖d x‖≤H) (R : ℕ) (hR : 0<R) (hRJ : R≤J)
    (a : ZMod J) (len : ℕ) :
    ‖complexIntervalSum (d-smoothComplexPositive (smoothingKernel R) d) a len‖ ≤
      12*H*(J:ℝ)/(R:ℝ) := by
  have hH0 : 0≤H := (norm_nonneg _).trans (hH 0)
  have hh := complex_interval_smoothing_bound d (smoothingKernel R) H hH
    (smoothing_kernel_mass hR) a len
  simp only [abs_of_nonneg (smoothing_kernel_nonneg R _)] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left (jackson_circular_first_moment R hR hRJ)
    (by positivity))).trans_eq (by ring)

end RHConnections.BlockFourier
