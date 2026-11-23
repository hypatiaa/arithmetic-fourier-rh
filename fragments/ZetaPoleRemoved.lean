import Verified
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
namespace RHConnections.PoleCompensation

def regularizedZeta : ℂ → ℂ :=
  Function.update (fun t : ℂ => (t-1) * riemannZeta t) 1 1

theorem regularizedZeta_one : regularizedZeta 1 = 1 := by
  simp [regularizedZeta]

theorem regularizedZeta_germ {s : ℂ} (hs : s ≠ 1) :
    regularizedZeta =ᶠ[nhds s] fun t => (t-1) * riemannZeta t := by
  filter_upwards [eventually_ne_nhds hs] with t ht
  exact Function.update_of_ne ht ..

theorem regularizedZeta_analytic (s : ℂ) : AnalyticAt ℂ regularizedZeta s := by
  have away : ∀ t : ℂ, t ≠ 1 → AnalyticAt ℂ regularizedZeta t := by
    intro t ht
    exact (((analyticAt_id.sub analyticAt_const).mul
      (analyticOn_riemannZeta t ht)).congr (regularizedZeta_germ ht).symm)
  rcases eq_or_ne s 1 with rfl | hs
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with t ht using (away t ht).differentiableAt
    · simpa only [regularizedZeta, continuousAt_update_same] using riemannZeta_residue_one
  · exact away s hs

def regularizedLogDerivative (s : ℂ) : ℂ :=
  -deriv regularizedZeta s / regularizedZeta s

theorem regularizedLogDerivative_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    regularizedLogDerivative s = compensatedLogDerivative s := by
  have hg := regularizedZeta_germ hs
  have hd : HasDerivAt (fun t : ℂ => (t-1)*riemannZeta t)
      (riemannZeta s + (s-1)*deriv riemannZeta s) s := by
    rw [show (fun t : ℂ => (t-1)*riemannZeta t) = (fun t : ℂ => t-1)*riemannZeta from rfl]
    simpa only [id_eq, one_mul] using ((hasDerivAt_id s).sub_const 1).mul
      (differentiableAt_riemannZeta hs).hasDerivAt
  rw [regularizedLogDerivative, hg.deriv_eq, hd.deriv, hg.eq_of_nhds, compensatedLogDerivative]
  field_simp [hz, sub_ne_zero.mpr hs] <;> ring

theorem regularizedLogDerivative_analytic {s : ℂ} (hs : regularizedZeta s ≠ 0) :
    AnalyticAt ℂ regularizedLogDerivative s :=
  (regularizedZeta_analytic s).deriv.neg.div (regularizedZeta_analytic s) hs

theorem regularizedLogDerivative_analytic_one : AnalyticAt ℂ regularizedLogDerivative 1 :=
  regularizedLogDerivative_analytic (regularizedZeta_one.trans_ne one_ne_zero)

theorem regularizedLogDerivative_on_halfplane {b : ℝ}
    (hzero : ∀ s : ℂ, b < s.re → riemannZeta s ≠ 0) :
    AnalyticOnNhd ℂ regularizedLogDerivative {s : ℂ | b < s.re} := by
  intro s hs
  by_cases h : s = 1
  · subst s
    exact regularizedLogDerivative_analytic_one
  · apply regularizedLogDerivative_analytic
    rw [(regularizedZeta_germ h).eq_of_nhds]
    exact mul_ne_zero (sub_ne_zero.mpr h) (hzero s hs)

theorem riemannHypothesis_iff_compensated_extension :
    RiemannHypothesis ↔ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s : ℂ | 1/2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → F s = compensatedLogDerivative s := by
  constructor
  · intro hRH
    refine ⟨regularizedLogDerivative, regularizedLogDerivative_on_halfplane ?_, ?_⟩
    · intro s hs hz
      have hs1 : s ≠ 1 := by
        rintro rfl
        exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hz
      have hnt : ¬∃ n : ℕ, s = -2 * (n+1) := by
        rintro ⟨n,rfl⟩
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        simp at hs <;> linarith
      exact (ne_of_gt hs) (hRH s hz hnt hs1)
    · intro s hs
      exact regularizedLogDerivative_eq (fun h => by simpa [h] using hs)
        (riemannZeta_ne_zero_of_one_le_re hs.le)
  · rintro ⟨F,hF,hEuler⟩
    exact riemannHypothesis_of_compensated_extension hF hEuler

end RHConnections.PoleCompensation
