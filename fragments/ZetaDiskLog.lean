import Verified
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Filter Metric
open scoped Topology
namespace RHConnections.ZetaDiskLog

theorem analytic_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball c R))
    (hn : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball c R) ∧ G c = Complex.log (f c) ∧
      ∀ z ∈ ball c R, Complex.exp (G z) = f z := by
  let U := ball c R
  have hU : IsOpen U := isOpen_ball
  have hc : c ∈ U := mem_ball_self hR
  have hUsc : IsSimplyConnected U := by
    letI : ContractibleSpace U := (convex_ball c R).contractibleSpace ⟨c,hc⟩
    exact (inferInstance : SimplyConnectedSpace U)
  have hcf : ContinuousOn f U := fun z hz => (hf z hz).continuousAt.continuousWithinAt
  obtain ⟨g,hg,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUsc hU
    (g := f) hcf (fun ⟨z,hz,h0⟩ => hn z hz h0)
  have heq (z : ℂ) (hz : z ∈ U) : Complex.exp (g z) = f z := he hz
  have hga (z : ℂ) (hz : z ∈ U) : AnalyticAt ℂ g z := by
    have ha : AnalyticAt ℂ Complex.exp (g z) := by fun_prop
    have hd : deriv Complex.exp (g z) ≠ 0 := by simp
    let L := ha.hasStrictDerivAt.localInverse _ _ _ hd
    have hL : AnalyticAt ℂ L (f z) := by
      rw [← heq z hz]
      exact ha.analyticAt_localInverse hd
    apply (hL.comp (hf z hz)).congr
    have hc := (hg z hz).continuousAt (hU.mem_nhds hz)
    filter_upwards [hc.tendsto.eventually (ha.hasStrictDerivAt.eventually_left_inverse hd),
      hU.mem_nhds hz] with t ht htU
    exact (congrArg L (heq t htU).symm).trans ht
  let G := fun z => g z-g c+Complex.log (f c)
  refine ⟨G, fun z hz => ((hga z hz).sub analyticAt_const).add analyticAt_const, ?_, ?_⟩
  · simp [G]
  · intro z hz
    simp only [G, Complex.exp_add, Complex.exp_sub, heq z hz, heq c hc,
      Complex.exp_log (hn c hc), div_mul_cancel₀ _ (hn c hc)]

theorem log_branch_eq_principal_on_positive_ball {f G : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball c r))
    (hG : AnalyticOnNhd ℂ G (ball c r)) (hc : G c = Complex.log (f c))
    (hpos : ∀ z ∈ ball c r, 0 < (f z).re)
    (he : ∀ z ∈ ball c r, Complex.exp (G z) = f z) :
    Set.EqOn G (fun z => Complex.log (f z)) (ball c r) := by
  let U := ball c r
  have hU : IsOpen U := isOpen_ball
  have hcU : c ∈ U := mem_ball_self hr
  have hPL : AnalyticOnNhd ℂ (fun z => Complex.log (f z)) U := by
    intro z hz
    have hs : f z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (hpos z hz)
    exact (analyticAt_clog hs).comp (hf z hz)
  apply hG.eqOn_of_preconnected_of_eventuallyEq hPL (convex_ball c r).isPreconnected hcU
  have ha : AnalyticAt ℂ Complex.exp (G c) := by fun_prop
  have hd : deriv Complex.exp (G c) ≠ 0 := by simp
  let L := ha.hasStrictDerivAt.localInverse _ _ _ hd
  have hloc : ∀ᶠ x in nhds (G c), L (Complex.exp x) = x :=
    ha.hasStrictDerivAt.eventually_left_inverse hd
  have hloc' : ∀ᶠ x in nhds (Complex.log (f c)), L (Complex.exp x) = x := by
    rw [← hc]
    exact hloc
  have hPLc : ContinuousAt (fun z => Complex.log (f z)) c := (hPL c hcU).continuousAt
  have hlocPL : ∀ᶠ x in nhds c, L (Complex.exp (Complex.log (f x))) = Complex.log (f x) :=
    hPLc.tendsto.eventually hloc'
  filter_upwards [(hG c hcU).continuousAt.tendsto.eventually hloc, hlocPL, hU.mem_nhds hcU]
    with z hz hz' hzU
  have hf0 : f z ≠ 0 := fun heq =>
    (lt_irrefl (0:ℝ)) (by simpa [heq] using hpos z hzU)
  rw [he z hzU] at hz
  rw [Complex.exp_log hf0] at hz'
  exact hz.symm.trans hz'

end RHConnections.ZetaDiskLog
