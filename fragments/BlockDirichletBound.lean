import Verified
import BlockIntervalShift

noncomputable section
namespace RHConnections.RankPairing

private theorem norm_exp_double_angle_sub_one (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ Real.pi) :
    ‖Complex.exp ((↑(2 * x) : ℂ) * Complex.I) - 1‖ = 2 * Real.sin x := by
  have hre : (Complex.exp ((↑(2 * x) : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
    rw [Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im]
  have him : (Complex.exp ((↑(2 * x) : ℂ) * Complex.I)).im = Real.sin (2 * x) := by
    rw [Complex.exp_im]
    simp [Complex.mul_re, Complex.mul_im]
  have hs : ‖Complex.exp ((↑(2 * x) : ℂ) * Complex.I) - 1‖ ^ 2 =
      (2 * Real.sin x) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    nlinarith only [Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_eq_half_sub x]
  have hxsin := Real.sin_nonneg_of_nonneg_of_le_pi hx hx'
  calc
    _ = Real.sqrt (‖Complex.exp ((↑(2 * x) : ℂ) * Complex.I) - 1‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = 2 * Real.sin x := by rw [hs, Real.sqrt_sq (by positivity)]

theorem block_character_chord {J : ℕ} [NeZero J] (h : ZMod J) :
    ‖ZMod.stdAddChar h - 1‖ =
      2 * Real.sin (Real.pi * (blockCyclicDistance h : ℝ) / (J : ℝ)) := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne J)
  have hv : (h.val : ℝ) ≤ J := by exact_mod_cast (ZMod.val_lt h).le
  have hphase : 2 * (Real.pi : ℂ) * Complex.I * (h.val : ℂ) / (J : ℂ) =
      (↑(2 * (Real.pi * (h.val : ℝ) / (J : ℝ))) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hphase,
    norm_exp_double_angle_sub_one _ (by positivity) ((div_le_iff₀ hJ).2 (by
      gcongr))]
  by_cases he : h.val ≤ J - h.val
  · rw [blockCyclicDistance, min_eq_left he]
  · rw [blockCyclicDistance, min_eq_right (le_of_not_ge he), Nat.cast_sub (ZMod.val_lt h).le]
    rw [show Real.pi * ((J : ℝ) - (h.val : ℝ)) / (J : ℝ) =
        Real.pi - Real.pi * (h.val : ℝ) / (J : ℝ) by field_simp]
    rw [Real.sin_pi_sub]

theorem block_character_chord_lower {J : ℕ} [NeZero J] (h : ZMod J) :
    4 * (blockCyclicDistance h : ℝ) / (J : ℝ) ≤ ‖ZMod.stdAddChar h - 1‖ := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne J)
  have hd : 2 * blockCyclicDistance h ≤ J := by
    have hl := min_le_left h.val (J - h.val)
    have hr := min_le_right h.val (J - h.val)
    have hv := ZMod.val_lt h
    unfold blockCyclicDistance
    omega
  have hdr : 2 * (blockCyclicDistance h : ℝ) ≤ J := by exact_mod_cast hd
  have harg : Real.pi * (blockCyclicDistance h : ℝ) / (J : ℝ) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hJ).2
    nlinarith only [mul_le_mul_of_nonneg_left hdr Real.pi_pos.le]
  rw [block_character_chord]
  have hs := Real.mul_le_sin (by positivity) harg
  have heq : 2 / Real.pi * (Real.pi * (blockCyclicDistance h : ℝ) / (J : ℝ)) =
      2 * (blockCyclicDistance h : ℝ) / (J : ℝ) := by field_simp
  rw [heq] at hs
  calc
    _ = 2 * (2 * (blockCyclicDistance h : ℝ) / (J : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

def blockDirichletKernel {J : ℕ} [NeZero J] (R : ℕ) (h : ZMod J) : ℂ :=
  ∑ r ∈ Finset.range R, ZMod.stdAddChar ((r : ZMod J) * h)

theorem block_dirichlet_kernel_bound {J : ℕ} [NeZero J] (R : ℕ) (h : ZMod J) :
    (blockCyclicDistance h : ℝ) * ‖blockDirichletKernel R h‖ ≤ (J : ℝ) / 2 := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne J)
  have hgeom : blockDirichletKernel R h * (ZMod.stdAddChar h - 1) =
      (ZMod.stdAddChar h)^R - 1 := by
    unfold blockDirichletKernel
    simp_rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
    exact geom_sum_mul _ _
  have hbound : ‖blockDirichletKernel R h‖ * ‖ZMod.stdAddChar h - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      _ ≤ ‖(ZMod.stdAddChar h)^R‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, AddChar.norm_apply]; norm_num
  have hmul := mul_le_mul_of_nonneg_left (block_character_chord_lower h)
    (norm_nonneg (blockDirichletKernel R h))
  have hscaled : (4 * ((blockCyclicDistance h : ℝ) * ‖blockDirichletKernel R h‖)) /
      (J : ℝ) ≤ 2 := by
    convert hmul.trans hbound using 1
    ring
  linarith only [(div_le_iff₀ hJ).1 hscaled]

end RHConnections.RankPairing
