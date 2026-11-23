import Verified

open MeasureTheory Set HurwitzZeta
noncomputable section
namespace RHConnections.HurwitzTailGrowth
open SpectralTail WeakFEPairMellinSplit

private theorem upperF_measurable (P : WeakFEPair ℂ)
    (hP : ContinuousOn P.f (Set.Ioi (0:ℝ))) : Measurable (upperF P) := by
  have hh : upperF P = (Set.Ioi (1:ℝ)).indicator (fun x => P.f x-P.f₀) := by
    funext x
    by_cases hx : 1 < x
    · have hxi : x ∈ Set.Ioi (1:ℝ) := hx
      have hxo : x ∉ Set.Ioo (0:ℝ) 1 := Set.notMem_Ioo_of_ge hx.le
      simp [upperF, WeakFEPair.f_modif, hxi, hxo]
    · simp [upperF, hx]
  rw [hh]
  apply ContinuousOn.measurable_piecewise _ continuous_zero.continuousOn measurableSet_Ioi
  exact (hP.mono fun _ hx => zero_lt_one.trans (Set.mem_Ioi.mp hx)).sub continuousOn_const

private theorem mellin_upper_growth {g : ℝ → ℂ} (hm : Measurable g)
    (h0 : ∀ x ≤ 1, g x = 0)
    (hg : ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x → ‖g x‖ ≤ C*Real.exp (-p*x))
    (u : ℂ → ℂ)
    (hu : ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ R → (u s).re-1 ≤ R) :
    MellinGrowthEnvelope (fun s => mellin g (u s)) := by
  obtain ⟨p,C,hp,hC,hg⟩ := hg
  let B : ℝ := 1+2/p
  let D : ℝ := 1+Real.log B/Real.log 2
  have hB : 1 ≤ B := by dsimp [B]; linarith [show 0 ≤ 2/p by positivity]
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  refine ⟨C*(2/p),D,by positivity,by dsimp [D]; positivity,?_⟩
  intro R hR s hs
  have hr : 0 < R := by linarith
  have hcomp : Real.log (1+2*R/p) ≤ D*Real.log R := by
    calc
      _ ≤ Real.log (B*R) := by
        apply Real.log_le_log (by positivity)
        dsimp [B]
        rw [show (1+2/p)*R=R+2*R/p by ring]
        linarith
      _ = Real.log B+Real.log R := Real.log_mul (by linarith) hr.ne'
      _ ≤ (Real.log B/Real.log 2)*Real.log R+Real.log R := by
        apply add_le_add_left
        calc
          _ = (Real.log B/Real.log 2)*Real.log (2:ℝ) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hR)
            (div_nonneg hlogB hlog.le)
      _ = _ := by dsimp [D]; ring
  calc
    _ ≤ (C*Real.exp (R*Real.log (1+2*R/p)))*(2/p) :=
      (mellin_exp_tail_bound g hm h0 hp hC hr.le hg (u s) (hu R hR s hs)).2
    _ = (C*(2/p))*Real.exp (R*Real.log (1+2*R/p)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ R*(D*Real.log R) := mul_le_mul_of_nonneg_left hcomp hr.le
        _ = _ := by ring

private theorem weak_mellin_envelope (P : WeakFEPair ℂ)
    (hF : ContinuousOn P.f (Set.Ioi 0)) (hG : ContinuousOn P.g (Set.Ioi 0))
    (hdecF : ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
      ‖P.f_modif x‖ ≤ C*Real.exp (-p*x))
    (hdecG : ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
      ‖P.g_modif x‖ ≤ C*Real.exp (-p*x))
    (u : ℂ → ℂ)
    (hu : ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ R → (u s).re-1 ≤ R)
    (hu' : ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ R → ((P.k:ℂ)-u s).re-1 ≤ R) :
    MellinGrowthEnvelope (fun s => P.Λ₀ (u s)) := by
  have hupper (Q : WeakFEPair ℂ)
      (h : ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
        ‖Q.f_modif x‖ ≤ C*Real.exp (-p*x)) :
      ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 < x →
        ‖upperF Q x‖ ≤ C*Real.exp (-p*x) := by
    obtain ⟨p,C,hp,hC,h⟩ := h
    refine ⟨p,C,hp,hC, fun x hx => ?_⟩
    simpa [upperF, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)] using h x hx
  have hz (Q : WeakFEPair ℂ) (x : ℝ) (hx : x ≤ 1) : upperF Q x = 0 :=
    Set.indicator_of_notMem (show x ∉ Set.Ioi (1:ℝ) from not_lt.mpr hx) _
  have ha := mellin_upper_growth (upperF_measurable P hF) (hz P) (hupper P hdecF) u hu
  have hb := mellin_upper_growth (upperF_measurable P.symm hG) (hz P.symm)
    (hupper P.symm hdecG) (fun s => (P.k:ℂ)-u s) hu'
  have h := ha.add (hb.const_mul P.ε)
  simp_rw [weakFEPair_mellin_split, smul_eq_mul]
  exact h

theorem completed_hurwitz_even_envelope (a : UnitAddCircle) :
    MellinGrowthEnvelope (completedHurwitzZetaEven₀ a) := by
  have h := weak_mellin_envelope (hurwitzEvenFEPair a)
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a))
    (hurwitzEven_tail_decay a).1 (hurwitzEven_tail_decay a).2 (fun s => s/2)
    (by
      intro R hR s hs
      norm_num [Complex.div_re]
      linarith [(Complex.re_le_norm s).trans hs])
    (by
      intro R hR s hs
      have hneg : -s.re ≤ R := by simpa only [Complex.neg_re,norm_neg] using
        (Complex.re_le_norm (-s)).trans (by simpa only [norm_neg] using hs)
      norm_num [hurwitzEvenFEPair, Complex.sub_re, Complex.div_re]
      linarith)
  have hh := h.const_mul (1/2:ℂ)
  unfold completedHurwitzZetaEven₀
  convert hh using 1
  ext s
  ring

theorem completed_hurwitz_odd_envelope (a : UnitAddCircle) :
    MellinGrowthEnvelope (completedHurwitzZetaOdd a) := by
  have h := weak_mellin_envelope (hurwitzOddFEPair a)
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a))
    (hurwitzOdd_tail_decay a).1 (hurwitzOdd_tail_decay a).2 (fun s => (s+1)/2)
    (by
      intro R hR s hs
      norm_num [Complex.div_re, Complex.add_re]
      linarith [(Complex.re_le_norm s).trans hs])
    (by
      intro R hR s hs
      have hneg : -s.re ≤ R := by simpa only [Complex.neg_re,norm_neg] using
        (Complex.re_le_norm (-s)).trans (by simpa only [norm_neg] using hs)
      norm_num [hurwitzOddFEPair, Complex.sub_re, Complex.div_re, Complex.add_re]
      linarith)
  have h0 (s : ℂ) : (hurwitzOddFEPair a).Λ s = (hurwitzOddFEPair a).Λ₀ s := by
    rw [WeakFEPair.Λ]
    simp [hurwitzOddFEPair]
  have hh := h.const_mul (1/2:ℂ)
  unfold completedHurwitzZetaOdd
  simp_rw [h0]
  convert hh using 1
  ext s
  ring

end RHConnections.HurwitzTailGrowth
