import Verified

open Metric
namespace RHConnections.SpectralTail

theorem entireXi_jensen_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ s ∈ sphere (2:ℂ) R, Real.log ‖entireXi s‖ ≤ C*(R+2)*Real.log (R+2) := by
  obtain ⟨p, C, hp, hC, hΛ⟩ := completed_zeta_mellin_growth
  let B : ℝ := 1+2/p
  let A : ℝ := 2*(C*(2/p))+1
  have hB : 1 ≤ B := by dsimp [B]; linarith [show 0 ≤ 2/p by positivity]
  have hA : 1 ≤ A := by dsimp [A]; linarith [show 0 ≤ C*(2/p) by positivity]
  have hlog₂ := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hAl : 0 ≤ Real.log A := Real.log_nonneg hA
  have hBl : 0 ≤ Real.log B := Real.log_nonneg hB
  refine ⟨Real.log A / Real.log 2 + 3 + Real.log B / Real.log 2, by positivity, ?_⟩
  intro R hR s hs
  let u : ℝ := R+2
  have hu : 2 ≤ u := by dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hsu : ‖s‖ ≤ u := by
    have hd : ‖s-(2:ℂ)‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hs
    calc
      ‖s‖ = ‖s-2+2‖ := by rw [sub_add_cancel]
      _ ≤ ‖s-2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ = u := by rw [hd, Complex.norm_two]
  have hs₁ : ‖s-1‖ ≤ 2*u := by
    have h := norm_sub_le s (1:ℂ)
    simp only [norm_one] at h
    linarith
  have hpos (y : ℂ) : y.re ≤ ‖y‖ := Complex.re_le_norm _
  have hsre : (s/2).re - 1 ≤ u := by norm_num [Complex.div_re]; linarith [hpos s]
  have hsre' : ((1-s)/2).re - 1 ≤ u := by
    norm_num [Complex.div_re, Complex.sub_re]
    have hh := hpos (-s)
    simp only [Complex.neg_re, norm_neg] at hh
    linarith
  have hL := hΛ s u hu0.le hsre hsre'
  have hBu : 0 < 1+2*u/p := by positivity
  have hBlog : Real.log (1+2*u/p) ≤ Real.log (B*u) := by
    apply Real.log_le_log hBu
    dsimp [B]
    have hh : (1+2/p)*u = u + 2*u/p := by ring
    rw [hh]
    linarith
  let E := Real.exp (u*Real.log (B*u))
  have hE : 1 ≤ E := by
    dsimp [E]
    apply Real.one_le_exp
    exact mul_nonneg hu0.le (Real.log_nonneg (by nlinarith))
  have hnorm : ‖entireXi s‖ ≤ A*u^2*E := calc
    _ ≤ (‖s‖*‖s-1‖)*‖completedRiemannZeta₀ s‖+1 := by
      simpa only [entireXi, norm_mul, norm_one] using
        norm_add_le (s*(s-1)*completedRiemannZeta₀ s) (1:ℂ)
    _ ≤ (u*(2*u))*((C*(2/p))*E)+1 := by
      apply add_le_add_left
      apply mul_le_mul (mul_le_mul hsu hs₁ (norm_nonneg _) (by positivity)) _
        (norm_nonneg _) (by positivity)
      exact hL.trans (by
        calc
          _ ≤ (C*E)*(2/p) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ hC
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hBlog hu0.le)
          _ = _ := by ring)
    _ ≤ _ := by
      have h0 : 1 ≤ u^2*E := by
        exact one_le_mul_of_one_le_of_one_le (by nlinarith) hE
      dsimp [A]
      nlinarith
  have hlu : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hlu₀ : 0 ≤ Real.log u := hlog₂.le.trans hlu
  have hcoeff : 0 ≤ Real.log A / Real.log 2 + 3 + Real.log B / Real.log 2 := by positivity
  by_cases hzero : entireXi s = 0
  · rw [hzero, norm_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg hcoeff hu0.le) hlu₀
  have hlog := Real.log_le_log (norm_pos_iff.mpr hzero) hnorm
  have hlogE : Real.log E = u*(Real.log B+Real.log u) := by
    dsimp [E]
    rw [Real.log_exp, Real.log_mul (by linarith) hu0.ne']
  rw [Real.log_mul (by positivity : A*u^2 ≠ 0) (by positivity : E ≠ 0),
    Real.log_mul (by linarith : A ≠ 0) (by positivity : u^2 ≠ 0), Real.log_pow, hlogE] at hlog
  have hAl' : Real.log A ≤ (Real.log A/Real.log 2) * Real.log u := by
    calc
      _ = (Real.log A/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlu (by positivity)
  have hBl' : Real.log B ≤ (Real.log B/Real.log 2) * Real.log u := by
    calc
      _ = (Real.log B/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlu (by positivity)
  change Real.log ‖entireXi s‖ ≤ _ * u * Real.log u
  calc
    _ ≤ Real.log A + 2*Real.log u + u*(Real.log B+Real.log u) := hlog
    _ ≤ _ := by
      have hAA := mul_le_mul_of_nonneg_right hAl' hu0.le
      have hBB := mul_le_mul_of_nonneg_right hBl' hu0.le
      have hA₁ := mul_le_mul_of_nonneg_left (show 1 ≤ u by linarith) hAl
      have hU := mul_le_mul_of_nonneg_left (show 1 ≤ u by linarith) hlu₀
      nlinarith

theorem zeta_quantitative_zero_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (s : Finset NontrivialZetaZero), 1 ≤ T →
      (∀ r ∈ s, |r.val.im| ≤ T) →
      (∑ r ∈ s, (analyticOrderNatAt riemannZeta r.val : ℝ)) ≤ C * (T+2) * Real.log (T+2) := by
  classical
  obtain ⟨C, hC, hG⟩ := entireXi_jensen_growth
  let D := (6*C + |Real.log ‖entireXi 2‖|/Real.log 2)/Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro T s hT hs
  let e : NontrivialZetaZero ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  have h := jensen_strip_zero_count entireXi_analytic entireXi_two_ne_zero C hC hG
    T hT (s.map e) (by
      intro z hz
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hz
      exact ⟨r.property.1.1.le, r.property.1.2.le, hs r hr⟩)
  simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) h
  intro r _
  have hne : r.val ≠ 1 := by
    intro he
    have hl' := r.property.1.2
    rw [he, Complex.one_re] at hl'
    exact (lt_irrefl _) hl'
  change (analyticOrderNatAt riemannZeta r.val : ℝ) = (analyticOrderNatAt entireXi r.val : ℝ)
  unfold analyticOrderNatAt
  rw [entireXi_order_eq_zeta r.property.1.1 hne]

end RHConnections.SpectralTail
