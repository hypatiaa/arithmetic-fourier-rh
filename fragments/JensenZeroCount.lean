import Verified
import Mathlib.Analysis.Complex.JensenFormula

noncomputable section
namespace RHConnections.SpectralTail

open MeromorphicOn Metric

theorem jensen_finite_subset {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hf : ∀ z, AnalyticAt ℂ f z) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (2*r), ‖f z‖ ≤ M)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    (∑ z ∈ S, (analyticOrderNatAt f z : ℝ)) ≤ Real.log (M/‖f c‖) / Real.log 2 := by
  classical
  have hi : AnalyticOnNhd ℂ f (closedBall c r) := fun z _ => hf z
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := 2*r) (M := M)
    (f := f) (by simpa [abs_of_pos hr]) (by rw [abs_of_pos hr, abs_of_pos (by positivity)]; linarith)
    hM (fun z _ => hf z) hc (by simpa [abs_of_pos (show 0 < 2*r by positivity)] using hbound)
  rw [abs_of_pos hr, show 2*r/r = 2 by field_simp [hr.ne'] ] at hJ
  let d := divisor f (closedBall c r)
  have hd := d.finiteSupport (isCompact_closedBall c r)
  let U := S ∪ hd.toFinset
  have hsup : Function.support (fun z => d z) ⊆ (U : Set ℂ) := by
    intro z hz
    exact Finset.mem_union_right S (hd.mem_toFinset.mpr hz)
  have he : ∀ z ∈ S, (analyticOrderNatAt f z : ℤ) = d z := by
    intro z hz
    change _ = divisor f (closedBall c r) z
    rw [hi.divisor_apply (hS z hz)]
    unfold analyticOrderNatAt
    cases analyticOrderAt f z using ENat.recTopCoe <;> rfl
  have hle : (∑ z ∈ S, (analyticOrderNatAt f z : ℤ)) ≤ ∑ᶠ z, d z := by
    rw [finsum_eq_sum_of_support_subset _ hsup, Finset.sum_congr rfl he]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      (fun z _ _ => hi.divisor_nonneg z)
  apply le_trans _ hJ
  exact_mod_cast hle

theorem jensen_strip_zero_count {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (h2 : f 2 ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∀ z ∈ sphere (2:ℂ) R,
      Real.log ‖f z‖ ≤ C*(R+2)*Real.log (R+2))
    (T : ℝ) (hT : 1 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    (∑ z ∈ S, (analyticOrderNatAt f z : ℝ)) ≤
      ((6*C + |Real.log ‖f 2‖|/Real.log 2)/Real.log 2) * (T+2) * Real.log (T+2) := by
  let r := T+2
  have hr : 3 ≤ r := by dsimp [r]; linarith
  have hrp : 0 < r := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B := C*(2*r+2)*Real.log (2*r+2)
  have hBp : 0 ≤ B := mul_nonneg (mul_nonneg hC (by linarith)) (Real.log_nonneg (by linarith))
  have hM : 1 ≤ Real.exp B := Real.one_le_exp hBp
  have hb : ∀ z ∈ sphere (2:ℂ) (2*r), ‖f z‖ ≤ Real.exp B := by
    intro z hz
    by_cases hn : f z = 0
    · simp [hn, (Real.exp_pos B).le]
    · rw [← Real.exp_log (norm_pos_iff.mpr hn)]
      exact Real.exp_le_exp.mpr (hgrowth _ (by linarith) z hz)
  have hs : ∀ z ∈ S, z ∈ closedBall (2:ℂ) r := by
    intro z hz
    obtain ⟨h0,h1,hI⟩ := hS z hz
    rw [mem_closedBall, dist_eq_norm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    norm_num [Complex.sub_re, Complex.sub_im]
    rw [abs_of_nonpos (by linarith : z.re - 2 ≤ 0)]
    dsimp [r]
    linarith
  have hJ := jensen_finite_subset hrp hM hf h2 hb S hs
  rw [Real.log_div (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr h2), Real.log_exp] at hJ
  have hlogr : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) (by linarith)
  have hscale : 2*r+2 ≤ r*r := by nlinarith [mul_nonneg (by linarith : 0 ≤ r-3) hrp.le]
  have hlogR : Real.log (2*r+2) ≤ 2*Real.log r := by
    have h := Real.log_le_log (by linarith : 0 < 2*r+2) hscale
    rwa [Real.log_mul hrp.ne' hrp.ne', ← two_mul] at h
  have hsmall : 2*r+2 ≤ 3*r := by linarith
  have hBB : B ≤ (6*C)*(r*Real.log r) := by
    calc B ≤ C*(3*r)*(2*Real.log r) := by
          dsimp [B]; gcongr <;> exact Real.log_nonneg (by linarith)
      _ = _ := by ring
  have hW : Real.log 2 ≤ r*Real.log r := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ r-1) (le_trans hlog.le hlogr)]
  have hbase : |Real.log ‖f 2‖| ≤ (|Real.log ‖f 2‖|/Real.log 2)*(r*Real.log r) := by
    calc |Real.log ‖f 2‖| = (|Real.log ‖f 2‖|/Real.log 2)*Real.log 2 := by field_simp [hlog.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (div_nonneg (abs_nonneg _) hlog.le)
  apply hJ.trans
  change (B-Real.log ‖f 2‖)/Real.log 2 ≤
    ((6*C+|Real.log ‖f 2‖|/Real.log 2)/Real.log 2)*r*Real.log r
  rw [div_le_iff₀ hlog]
  calc B-Real.log ‖f 2‖ ≤ (6*C)*(r*Real.log r) +
        (|Real.log ‖f 2‖|/Real.log 2)*(r*Real.log r) := by
          linarith [neg_le_abs (Real.log ‖f 2‖)]
    _ = _ := by field_simp [hlog.ne'] <;> ring

end RHConnections.SpectralTail
