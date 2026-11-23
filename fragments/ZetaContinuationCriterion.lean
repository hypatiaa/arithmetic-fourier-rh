import Verified
import Mathlib.Analysis.Complex.Convex

namespace RHConnections.PoleCompensation

private def puncturedRight (b : ℝ) : Set ℂ := {s | b < s.re ∧ s ≠ 1}

private theorem puncturedRight_preconnected {b : ℝ} (hb : b < 1) : IsPreconnected (puncturedRight b) := by
  let H : Set ℂ := {s | b < s.re}
  let R : Set ℂ := {s | 1 < s.re}
  let A : Set ℂ := H ∩ {s | 0 < s.im}
  let B : Set ℂ := H ∩ {s | s.im < 0}
  let L : Set ℂ := H ∩ {s | s.re < 1}
  have hH : Convex ℝ H := convex_halfSpace_re_gt _
  have hR : IsPreconnected R := (convex_halfSpace_re_gt 1).isPreconnected
  have hA : IsPreconnected A := (hH.inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected B := (hH.inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hL : IsPreconnected L := (hH.inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hRA : IsPreconnected (R ∪ A) := IsPreconnected.union (2 + Complex.I)
    (by norm_num [R]) (by norm_num [A,H] <;> linarith) hR hA
  have hRAB : IsPreconnected ((R ∪ A) ∪ B) := IsPreconnected.union (2 - Complex.I)
    (Or.inl (by norm_num [R])) (by norm_num [B,H] <;> linarith) hRA hB
  have hAll : IsPreconnected (((R ∪ A) ∪ B) ∪ L) := IsPreconnected.union
    (⟨(b+1)/2,1⟩ : ℂ) (Or.inl (Or.inr (by norm_num [A,H] <;> linarith)))
    (by change b < (b+1)/2 ∧ (b+1)/2 < 1; constructor <;> linarith) hRAB hL
  have he : puncturedRight b = (((R ∪ A) ∪ B) ∪ L) := by
    ext s
    change (b < s.re ∧ s ≠ 1) ↔
      (((1 < s.re ∨ (b < s.re ∧ 0 < s.im)) ∨
        (b < s.re ∧ s.im < 0)) ∨ (b < s.re ∧ s.re < 1))
    constructor
    · rintro ⟨hs,hn⟩
      by_contra h
      push_neg at h
      apply hn
      apply Complex.ext <;> simp <;> grind
    · intro h
      constructor
      · rcases h with ((h|h)|h)|h <;> grind
      · rintro rfl
        norm_num at h
  rwa [he]

theorem zeta_zero_free_above_compensated_extension {b : ℝ} (hb : b < 1) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | b < s.re})
    (hEuler : ∀ s : ℂ, 1 < s.re → F s = compensatedLogDerivative s)
    {s : ℂ} (hs : b < s.re) : riemannZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hOpen : IsOpen (puncturedRight b) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have h2 : (2 : ℂ) ∈ puncturedRight b := by norm_num [puncturedRight] <;> linarith
  let g := fun t : ℂ => -(F t + 1/(t-1))
  have hg : AnalyticOnNhd ℂ g (puncturedRight b) := by
    intro t ht
    exact ((hF t ht.1).add (analyticAt_const.div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr ht.2))).neg
  have ha : deriv riemannZeta =ᶠ[nhds (2:ℂ)] fun t => g t * riemannZeta t := by
    have hnear : {t : ℂ | 1 < t.re} ∈ nhds (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear] with t ht
    have hn := riemannZeta_ne_zero_of_one_le_re (s := t) (le_of_lt ht)
    dsimp [g]
    rw [hEuler t ht, compensatedLogDerivative]
    rw [sub_add_cancel, neg_div, neg_neg, div_mul_cancel₀ _ hn]
  exact no_zero_of_logDerivative_extension hOpen (puncturedRight_preconnected hb) h2
    (fun t ht => analyticOn_riemannZeta t ht.2) hg
    (riemannZeta_ne_zero_of_one_le_re (by norm_num)) ha s ⟨hs,hs1⟩

theorem zeta_zero_free_of_compensated_extension {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | 1/2 < s.re})
    (hEuler : ∀ s : ℂ, 1 < s.re → F s = compensatedLogDerivative s)
    {s : ℂ} (hs : 1/2 < s.re) : riemannZeta s ≠ 0 :=
  zeta_zero_free_above_compensated_extension (by norm_num : (1/2 : ℝ) < 1) hF hEuler hs

theorem riemannHypothesis_of_right_zero_free
    (hfree : ∀ s : ℂ, 1/2 < s.re → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num [riemannZeta_zero] at hz
  have hg : Complex.Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n,hn⟩
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ k =>
      apply htriv
      exact ⟨k, by simpa [Nat.cast_succ, neg_mul] using hn⟩
  have hc : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
    exact hz.resolve_right hg
  have hdual : riemannZeta (1-s) = 0 := by
    rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr (Ne.symm hs1)),
      completedRiemannZeta_one_sub, hc, zero_div]
  apply le_antisymm
  · by_contra! h
    exact hfree s h hz
  · by_contra! h
    exact hfree (1-s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith : 1/2 < (1-s).re) hdual

theorem riemannHypothesis_of_compensated_extension {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | 1/2 < s.re})
    (hEuler : ∀ s : ℂ, 1 < s.re → F s = compensatedLogDerivative s) :
    RiemannHypothesis :=
  riemannHypothesis_of_right_zero_free (fun _ hs =>
    zeta_zero_free_of_compensated_extension hF hEuler hs)

end RHConnections.PoleCompensation
