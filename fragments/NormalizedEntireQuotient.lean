import Verified
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Convex.Contractible

noncomputable section
namespace RHConnections.NormalizedEntireQuotient
open Filter Real Metric CanonicalFactor AffineFromRealPart
open scoped Topology

private theorem entire_unit_log {q : ℂ → ℂ} (hunit : ∀ s, AnalyticAt ℂ q s ∧ q s ≠ 0)
    (hq0 : q 0 = 1) : ∃ G : ℂ → ℂ, (∀ s, AnalyticAt ℂ G s) ∧ G 0 = 0 ∧
      ∀ s, Complex.exp (G s) = q s := by
  have hU : IsSimplyConnected (Set.univ : Set ℂ) := by
    letI : ContractibleSpace (Set.univ : Set ℂ) :=
      (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
    exact (inferInstance : SimplyConnectedSpace (Set.univ : Set ℂ))
  obtain ⟨g,hg,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    (g := q) (fun s _ => (hunit s).1.continuousAt.continuousWithinAt)
    (fun ⟨s,_,hs⟩ => (hunit s).2 hs)
  have heq (s : ℂ) : Complex.exp (g s) = q s := he (Set.mem_univ s)
  have hga (s : ℂ) : AnalyticAt ℂ g s := by
    have ha : AnalyticAt ℂ Complex.exp (g s) := by fun_prop
    have hd : deriv Complex.exp (g s) ≠ 0 := by simp
    let L := ha.hasStrictDerivAt.localInverse _ _ _ hd
    have hL : AnalyticAt ℂ L (q s) := by
      rw [← heq s]
      exact ha.analyticAt_localInverse hd
    apply (hL.comp (hunit s).1).congr
    have hc := (continuousOn_univ.mp hg).continuousAt (x := s)
    filter_upwards [hc.tendsto.eventually (ha.hasStrictDerivAt.eventually_left_inverse hd)] with t ht
    exact (congrArg L (heq t).symm).trans ht
  refine ⟨fun s => g s-g 0, fun s => (hga s).sub analyticAt_const, sub_self _, ?_⟩
  intro s
  rw [Complex.exp_sub, heq, heq, hq0, div_one]

theorem exists_normalized_entire_factor {f p : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hp : ∀ z, AnalyticAt ℂ p z)
    (hf0 : f 0 = 1) (hp0 : p 0 = 1)
    (hord : ∀ z, ∃ n : ℕ, analyticOrderAt f z = n ∧ analyticOrderAt p z = n) :
    ∃ G : ℂ → ℂ, (∀ s, AnalyticAt ℂ G s) ∧ G 0 = 0 ∧
      ∀ s, f s = Complex.exp (G s) * p s := by
  let q := toMeromorphicNFOn (f/p) Set.univ
  have hm : MeromorphicOn (f/p) Set.univ :=
    fun s _ => (hf s).meromorphicAt.div (hp s).meromorphicAt
  have hunit (s : ℂ) : AnalyticAt ℂ q s ∧ q s ≠ 0 := by
    obtain ⟨n,ha,hb⟩ := hord s
    have hn : MeromorphicNFAt q s := meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)
    have ho : meromorphicOrderAt q s = 0 := by
      dsimp only [q]
      rw [meromorphicOrderAt_toMeromorphicNFOn hm (Set.mem_univ _),
        meromorphicOrderAt_div (hf s).meromorphicAt (hp s).meromorphicAt,
        (hf s).meromorphicOrderAt_eq, (hp s).meromorphicOrderAt_eq, ha, hb]
      simp
    exact ⟨hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp ho.ge,
      hn.meromorphicOrderAt_eq_zero_iff.mp ho⟩
  have hmul (s : ℂ) : q s * p s = f s := by
    by_cases h : p s = 0
    · obtain ⟨n,ha,hb⟩ := hord s
      have hz : f s = 0 := by
        by_contra hh
        have horder := (hf s).analyticOrderAt_eq_zero.mpr hh
        have hpo : analyticOrderAt p s = 0 := hb.trans (ha.symm.trans horder)
        exact (hp s).analyticOrderAt_eq_zero.mp hpo h
      rw [h, mul_zero, hz]
    · have hquot := (hf s).div (hp s) h
      dsimp only [q]
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (Set.mem_univ _),
        toMeromorphicNFAt_eq_self.mpr hquot.meromorphicNFAt]
      exact div_mul_cancel₀ _ h
  have hq0 : q 0 = 1 := by simpa [hf0,hp0] using hmul 0
  obtain ⟨G,hG,hG0,he⟩ := entire_unit_log hunit hq0
  exact ⟨G,hG,hG0,fun s => (hmul s).symm.trans (congrArg (fun z => z*p s) (he s).symm)⟩

theorem meanAbsRe_le_of_factor {f p G : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hpA : ∀ z, AnalyticAt ℂ p z) (hX0 : f 0 = 1) (hP0 : p 0 = 1) (hG : Differentiable ℂ G)
    (he : ∀ s, f s = Complex.exp (G s) * p s)
    {R A B : ℝ} (hR : 0 < R)
    (hx : ∀ s ∈ sphere (0:ℂ) R, Real.log ‖f s‖ ≤ A)
    (hp : ∀ s ∈ sphere (0:ℂ) R, Real.log ‖p s‖ ≤ B) :
    meanAbsRe G R ≤ 2 * max A B := by
  classical
  let X := fun s : ℂ => Real.log ‖f s‖
  let P := fun s : ℂ => Real.log ‖p s‖
  let U := fun s : ℂ => |(G s).re|
  let F := U+X+P
  let H := fun s : ℂ => if p s = 0 then 2*max A B else F s
  have hpU : AnalyticOnNhd ℂ p Set.univ := fun z _ => hpA z
  have hX : 0 ≤ circleAverage X 0 R := circleAverage_log_norm_nonneg_of_one hf hX0 hR
  have hP : 0 ≤ circleAverage P 0 R := circleAverage_log_norm_nonneg_of_one
    (fun z => hpU z (Set.mem_univ _)) hP0 hR
  have iU : CircleIntegrable U 0 R := ContinuousOn.circleIntegrable hR.le (Complex.continuous_re.comp hG.continuous).abs.continuousOn
  have iX : CircleIntegrable X 0 R := MeromorphicOn.circleIntegrable_log_norm
    (fun z _ => (hf z).meromorphicAt)
  have iP : CircleIntegrable P 0 R := MeromorphicOn.circleIntegrable_log_norm
    (fun z _ => (hpU z (Set.mem_univ _)).meromorphicAt)
  have hne : ∀ᶠ z in codiscreteWithin (sphere (0:ℂ) |R|), p z ≠ 0 :=
    codiscreteWithin_mono (Set.subset_univ _) (hpU.preimage_zero_mem_codiscreteWithin
      (hP0.trans_ne one_ne_zero) (Set.mem_univ _) isConnected_univ)
  have hFH : F =ᶠ[codiscreteWithin (sphere (0:ℂ) |R|)] H := by
    filter_upwards [hne] with z hz
    simp [H,hz]
  have hMean : circleAverage F 0 R ≤ 2*max A B := by
    rw [circleAverage_congr_codiscreteWithin hFH hR.ne']
    apply circleAverage_mono_on_of_le_circle (CircleIntegrable.congr_codiscreteWithin hFH ((iU.add iX).add iP))
    intro s hs
    have hs' : s ∈ sphere (0:ℂ) R := by simpa [abs_of_pos hR] using hs
    by_cases hz : p s = 0
    · simp [H,hz]
    · simp only [H, if_neg hz]
      have heq : X s = (G s).re + P s := by
        dsimp [X,P]
        rw [he s, norm_mul, Complex.norm_exp,
          Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr hz), Real.log_exp]
      have hXX : X s ≤ max A B := (hx s hs').trans (le_max_left _ _)
      have hPP : P s ≤ max A B := (hp s hs').trans (le_max_right _ _)
      change |(G s).re| + X s + P s ≤ _
      rcases le_total 0 (G s).re with h|h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
  change circleAverage (U+X+P) 0 R ≤ _ at hMean
  rw [circleAverage_add (iU.add iX) iP, circleAverage_add iU iX] at hMean
  change circleAverage U 0 R ≤ _
  linarith

end RHConnections.NormalizedEntireQuotient
