import Verified
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform

noncomputable section
namespace RHConnections.ChebyshevCriterion
open MeasureTheory Filter Asymptotics PoleCompensation
open scoped Topology

def mangoldtCoeff (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℝ)

def psi (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, mangoldtCoeff k

def psiError (x : ℝ) : ℂ := psi x - (x:ℂ)

def ChebyshevCancellation : Prop := ∀ ε : ℝ, 0 < ε →
  psiError =O[atTop] (fun x : ℝ => x^(1/2+ε))

private def cutError : ℝ → ℂ := (Set.Ioi (1:ℝ)).indicator psiError

def chebyshevContinuation (s : ℂ) : ℂ := 1 + s * mellin cutError (-s)

private theorem cut_local : LocallyIntegrableOn cutError (Set.Ioi 0) := by
  have hp : LocallyIntegrableOn psi (Set.Ici 0) := by
    unfold psi
    simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (m := 1) mangoldtCoeff
      (a := (0:ℝ)) le_rfl (locallyIntegrableOn_const (1:ℂ)))
  have hid : LocallyIntegrableOn (fun x : ℝ => (x:ℂ)) (Set.Ici (0:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.locallyIntegrableOn measurableSet_Ici
  have h : LocallyIntegrableOn psiError (Set.Ici 0) := hp.sub hid
  intro x hx
  obtain ⟨U,hU,hI⟩ := h.mono_set Set.Ioi_subset_Ici_self x hx
  exact ⟨U,hU,hI.indicator measurableSet_Ioi⟩

private theorem cut_growth (hM : ChebyshevCancellation) {ε : ℝ} (he : 0 < ε) :
    cutError =O[atTop] (fun x : ℝ => x^(1/2+ε)) := by
  obtain ⟨C,hC⟩ := isBigO_iff.mp (hM ε he)
  refine isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hC] with x hx hc
  simpa only [cutError, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)] using hc

theorem chebyshevContinuation_analytic (hm : ChebyshevCancellation) :
    AnalyticOnNhd ℂ chebyshevContinuation {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change (1/2 : ℝ) < s.re at hs
  let ε : ℝ := (s.re-1/2)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let b := -s.re-1
  have htop : cutError =O[atTop] (fun x : ℝ => x^(-(-(1/2+ε)))) := by
    simpa only [neg_neg] using cut_growth hm hε
  have hbot : cutError =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    have hh : ∀ᶠ x in 𝓝[>] (0:ℝ), x < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hh] with x hx
    simp [cutError, not_lt.mpr hx.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s) cut_local htop
    (by change -s.re < -(1/2+ε); dsimp [ε]; linarith) hbot
    (by change -s.re-1 < -s.re; linarith)
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  have hM := hd.comp s hneg
  have hc : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) s := by fun_prop
  exact (hc.add (differentiableAt_id.mul hM)).differentiableWithinAt

private theorem mellin_cut_eq (s : ℂ) : mellin cutError (-s) =
    ∫ x in Set.Ioi (1:ℝ), psiError x * (x:ℂ)^(-(s+1)) := by
  unfold mellin
  have he (x : ℝ) : (x:ℂ)^(-s-1) • cutError x =
      (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => psiError x * (x:ℂ)^(-(s+1))) x := by
    by_cases hx : x ∈ Set.Ioi (1:ℝ)
    · simp only [cutError, Set.indicator_of_mem hx, smul_eq_mul, show -s-1= -(s+1) by ring, mul_comm]
    · simp [cutError,Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num))]

private theorem error_integrable (hm : ChebyshevCancellation) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => psiError x * (x:ℂ)^(-(s+1))) (Set.Ioi 1) := by
  have ht : cutError =O[atTop] (fun x : ℝ => x^(-(-1:ℝ))) := by
    simpa only [neg_neg,show (1/2:ℝ)+1/2=1 by norm_num] using cut_growth hm (show (0:ℝ)<1/2 by norm_num)
  have hb : cutError =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [cutError,not_lt.mpr hx.le]
  have h := mellinConvergent_of_isBigO_rpow (s := -s) cut_local ht
    (by change -s.re < -1; linarith) hb (by change -s.re-1 < -s.re; linarith)
  unfold MellinConvergent at h
  apply (h.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [cutError,Set.indicator_of_mem hx,smul_eq_mul,show -s-1= -(s+1) by ring,mul_comm]

theorem chebyshevContinuation_euler (hm : ChebyshevCancellation) {s : ℂ} (hs : 1 < s.re) :
    chebyshevContinuation s = compensatedLogDerivative s := by
  have ho := (hm (1/2) (by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  change (fun n : ℕ => psiError (n:ℝ)) =O[atTop] (fun n : ℕ => (n:ℝ)^((1/2:ℝ)+1/2)) at ho
  rw [show (1/2:ℝ)+1/2=1 by norm_num] at ho
  have hi : (fun n : ℕ => (n:ℂ)) =O[atTop] (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1,Eventually.of_forall fun n => ?_⟩
    simp
  have hn : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mangoldtCoeff k) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    have he : (fun n : ℕ => psiError (n:ℝ)) + (fun n : ℕ => (n:ℂ)) =
        (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mangoldtCoeff k) := by
      funext n
      simp only [Pi.add_apply, psiError, psi, Nat.floor_natCast, Complex.ofReal_natCast, sub_add_cancel]
    exact he ▸ ho.add hi
  have hL : LSeries mangoldtCoeff s = -deriv riemannZeta s / riemannZeta s :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h := LSeries_eq_mul_integral mangoldtCoeff (by norm_num : (0:ℝ)≤1) hs
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hn
  have he (x : ℝ) (hx : x ∈ Set.Ioi (1:ℝ)) :
      psi x * (x:ℂ)^(-(s+1)) = psiError x * (x:ℂ)^(-(s+1)) + (x:ℂ)^(-s) := by
    have hpos : 0<x := by change 1<x at hx; linarith
    have hp : (x:ℂ)^(-(s+1))*(x:ℂ) = (x:ℂ)^(-s) := by
      calc
        _ = (x:ℂ)^(-(s+1))*(x:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
        _ = (x:ℂ)^((-(s+1))+1) := (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne')).symm
        _ = _ := by rw [show -(s+1)+1 = -s by ring]
    rw [← hp, psiError]
    ring
  change LSeries mangoldtCoeff s = s * ∫ x in Set.Ioi (1:ℝ), psi x*(x:ℂ)^(-(s+1)) at h
  have hneg : (-s).re < -1 := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add (error_integrable hm hs)
    (integrableOn_Ioi_cpow_of_lt hneg (by norm_num)),integral_Ioi_cpow_of_lt hneg (by norm_num),
    Complex.ofReal_one,Complex.one_cpow,← mellin_cut_eq] at h
  rw [chebyshevContinuation,compensatedLogDerivative,← hL,h]
  have h1 : s ≠ 1 := fun he => by simpa [he] using hs
  field_simp [sub_ne_zero.mpr h1,show -s+1 ≠ 0 by intro he; apply h1; linear_combination -he] <;> ring

theorem riemannHypothesis_of_chebyshev (hm : ChebyshevCancellation) : RiemannHypothesis :=
  riemannHypothesis_of_compensated_extension (chebyshevContinuation_analytic hm)
    (fun _ hs => chebyshevContinuation_euler hm hs)

theorem line_euler_residual_of_chebyshev (hm : ChebyshevCancellation) {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    ZetaLineEulerResidual z₀ :=
  (riemannHypothesis_iff_line_euler_residual hz₀).mp (riemannHypothesis_of_chebyshev hm)

end RHConnections.ChebyshevCriterion
