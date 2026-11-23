import Verified
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform

noncomputable section
namespace RHConnections.MertensCriterion
open MeasureTheory Filter Asymptotics PoleCompensation
open scoped Topology

def moebiusCoeff (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℤ)

def mertens (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, moebiusCoeff k

def MertensCancellation : Prop := ∀ ε : ℝ, 0 < ε →
  mertens =O[atTop] (fun x : ℝ => x^(1/2+ε))

private def cutMertens : ℝ → ℂ := (Set.Ioi (1:ℝ)).indicator mertens

def mertensReciprocal (s : ℂ) : ℂ := s * mellin cutMertens (-s)

private theorem cut_local : LocallyIntegrableOn cutMertens (Set.Ioi 0) := by
  have h : LocallyIntegrableOn mertens (Set.Ici 0) := by
    unfold mertens
    simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (m := 1) moebiusCoeff
      (a := (0:ℝ)) le_rfl (locallyIntegrableOn_const (1:ℂ)))
  intro x hx
  obtain ⟨U,hU,hI⟩ := h.mono_set Set.Ioi_subset_Ici_self x hx
  exact ⟨U,hU,hI.indicator measurableSet_Ioi⟩

private theorem cut_growth (hM : MertensCancellation) {ε : ℝ} (he : 0 < ε) :
    cutMertens =O[atTop] (fun x : ℝ => x^(1/2+ε)) := by
  obtain ⟨C,hC⟩ := isBigO_iff.mp (hM ε he)
  refine isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hC] with x hx hc
  simpa only [cutMertens, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)] using hc

theorem mertensReciprocal_analytic (hm : MertensCancellation) :
    AnalyticOnNhd ℂ mertensReciprocal {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change (1/2 : ℝ) < s.re at hs
  let ε : ℝ := (s.re-1/2)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let b := -s.re-1
  have htop : cutMertens =O[atTop] (fun x : ℝ => x^(-(-(1/2+ε)))) := by
    simpa only [neg_neg] using cut_growth hm hε
  have hbot : cutMertens =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    have hh : ∀ᶠ x in 𝓝[>] (0:ℝ), x < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hh] with x hx
    simp [cutMertens, not_lt.mpr hx.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s) cut_local htop
    (by change -s.re < -(1/2+ε); dsimp [ε]; linarith) hbot
    (by change -s.re-1 < -s.re; linarith)
  exact (differentiableAt_id.mul (hd.comp s differentiableAt_id.neg)).differentiableWithinAt

private theorem mellin_cut_eq (s : ℂ) : mellin cutMertens (-s) =
    ∫ x in Set.Ioi (1:ℝ), mertens x * (x:ℂ)^(-(s+1)) := by
  unfold mellin
  have he (x : ℝ) : (x:ℂ)^(-s-1) • cutMertens x =
      (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => mertens x * (x:ℂ)^(-(s+1))) x := by
    by_cases hx : x ∈ Set.Ioi (1:ℝ)
    · simp only [cutMertens, Set.indicator_of_mem hx, smul_eq_mul, show -s-1= -(s+1) by ring, mul_comm]
    · simp [cutMertens,Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num))]

theorem mertensReciprocal_euler (hm : MertensCancellation) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mertensReciprocal s = 1 := by
  have ho := (hm (1/2) (by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hn : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, moebiusCoeff k) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    change (fun n : ℕ => mertens (n:ℝ)) =O[atTop] (fun n : ℕ => (n:ℝ)^((1/2:ℝ)+1/2)) at ho
    rw [show (1/2:ℝ)+1/2=1 by norm_num] at ho
    simpa only [mertens, Nat.floor_natCast] using ho
  have hconv : LSeriesSummable moebiusCoeff s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hi := LSeries_eq_mul_integral moebiusCoeff (by norm_num : (0:ℝ)≤1) hs hconv hn
  have hEq : LSeries moebiusCoeff s = mertensReciprocal s := by
    rw [mertensReciprocal,mellin_cut_eq]
    exact hi
  rw [← hEq, ← LSeries_one_eq_riemannZeta hs]
  exact LSeries_one_mul_Lseries_moebius hs

theorem right_zero_free_of_mertens (hm : MertensCancellation) :
    ∀ s : ℂ, 1/2 < s.re → riemannZeta s ≠ 0 := by
  let H : Set ℂ := {s | 1/2 < s.re}
  have hA : AnalyticOnNhd ℂ (regularizedZeta * mertensReciprocal) H :=
    (fun z hz => (regularizedZeta_analytic z).mul (mertensReciprocal_analytic hm z hz))
  have hB : AnalyticOnNhd ℂ (fun s : ℂ => s-1) H := fun _ _ => analyticAt_id.sub analyticAt_const
  have h2 : (2:ℂ) ∈ H := by norm_num [H]
  have hb : {s : ℂ | 1 < s.re} ∈ 𝓝 (2:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : regularizedZeta * mertensReciprocal =ᶠ[𝓝 (2:ℂ)] (fun s : ℂ => s-1) := by
    filter_upwards [hb] with z hz
    have hz1 : z ≠ 1 := by intro h; change 1 < z.re at hz; simpa [h] using hz
    change regularizedZeta z * mertensReciprocal z = z-1
    rw [(regularizedZeta_germ hz1).eq_of_nhds, mul_assoc, mertensReciprocal_euler hm hz, mul_one]
  have hall := hA.eqOn_of_preconnected_of_eventuallyEq hB (convex_halfSpace_re_gt (1/2)).isPreconnected h2 he
  intro s hs
  by_cases hs1 : s = 1
  · subst s; exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
  intro hz
  have h := hall (show s ∈ H from hs)
  change regularizedZeta s * mertensReciprocal s = s-1 at h
  rw [(regularizedZeta_germ hs1).eq_of_nhds,hz,mul_zero,zero_mul] at h
  exact (sub_ne_zero.mpr hs1) h.symm

theorem riemannHypothesis_of_mertens (hm : MertensCancellation) : RiemannHypothesis :=
  riemannHypothesis_of_right_zero_free (right_zero_free_of_mertens hm)

theorem line_euler_residual_of_mertens (hm : MertensCancellation) {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    ZetaLineEulerResidual z₀ :=
  (riemannHypothesis_iff_line_euler_residual hz₀).mp (riemannHypothesis_of_mertens hm)

end RHConnections.MertensCriterion
