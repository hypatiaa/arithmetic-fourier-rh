import Verified

namespace RHConnections.SpectralTail
open RelativeResolvent

theorem relative_vertical_norm_le {z : ℂ} (hz : z.re = 1) (r : NontrivialZetaZero) :
    ‖relative z 1 (r.val-(1/2:ℂ))‖ ≤
      16 * ‖z-1‖ * (1+2*‖z-1‖) / ‖r.val‖^2 := by
  let xi := r.val-(1/2:ℂ)
  let A := ‖z-xi‖
  let B := ‖(1:ℂ)-xi‖
  let D := ‖z-1‖
  have hxi : xi.re < 1/2 := by
    dsimp [xi]
    norm_num [Complex.sub_re, Complex.div_re]
    linarith [r.property.1.2]
  have hA : 1/2 ≤ A := by
    have h := Complex.re_le_norm (z-xi)
    rw [Complex.sub_re, hz] at h
    dsimp [A]
    linarith
  have hB : 1/2 ≤ B := by
    have h := Complex.re_le_norm ((1:ℂ)-xi)
    rw [Complex.sub_re, Complex.one_re] at h
    dsimp [B]
    linarith
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hD : 0 ≤ D := norm_nonneg _
  have hv : B ≤ (1+2*D)*A := by
    calc
      B = ‖(1-z)+(z-xi)‖ := by dsimp [B]; congr 1; ring
      _ ≤ D+A := by simpa [A,D,norm_sub_rev] using norm_add_le ((1:ℂ)-z) (z-xi)
      _ ≤ _ := by nlinarith [mul_nonneg hD (show 0 ≤ 2*A-1 by linarith)]
  have hrB : ‖r.val‖ ≤ 4*B := by
    calc
      _ = ‖(3/2:ℂ)-((1:ℂ)-xi)‖ := by congr 1; dsimp [xi]; ring
      _ ≤ 3/2+B := by simpa [B, norm_div] using norm_sub_le (3/2:ℂ) (1-xi)
      _ ≤ _ := by linarith
  have hsquare : ‖r.val‖^2 ≤ 16*(1+2*D)*(A*B) := by
    calc
      _ ≤ (4*B)^2 := pow_le_pow_left₀ (norm_nonneg _) hrB 2
      _ = 16*B*B := by ring
      _ ≤ 16*B*((1+2*D)*A) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by ring
  obtain ⟨δ,hδ,hd⟩ := zeta_zero_norm_lower
  have hr : 0 < ‖r.val‖ := hδ.trans_le (hd r)
  change ‖relative z 1 xi‖ ≤ 16*D*(1+2*D)/‖r.val‖^2
  rw [reference_subtraction z 1 xi (norm_pos_iff.mp hAp) (norm_pos_iff.mp hBp),
    norm_div, norm_mul, norm_sub_rev (1:ℂ) z]
  change D / (A*B) ≤ _
  apply (div_le_div_iff₀ (mul_pos hAp hBp) (sq_pos_of_pos hr)).mpr
  calc
    _ ≤ D*(16*(1+2*D)*(A*B)) := mul_le_mul_of_nonneg_left hsquare hD
    _ = _ := by ring

end RHConnections.SpectralTail
