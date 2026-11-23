import Verified
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Convex.Contractible

noncomputable section
namespace RHConnections.CanonicalFactor
open SpectralTail Filter
open scoped Topology

def xiProductQuotient : ℂ → ℂ := toMeromorphicNFOn (entireXi / zetaCanonicalProduct) Set.univ

private theorem quotient_meromorphic : MeromorphicOn (entireXi / zetaCanonicalProduct) Set.univ :=
  fun s _ => (entireXi_analytic s).meromorphicAt.div
    (zetaCanonicalProduct_entire s (Set.mem_univ _)).meromorphicAt

theorem xi_product_orders (s : ℂ) : ∃ n : ℕ,
    analyticOrderAt entireXi s = n ∧ analyticOrderAt zetaCanonicalProduct s = n := by
  by_cases hz : entireXi s = 0
  · let r : NontrivialZetaZero := ⟨s, (entireXi_eq_zero_iff s).mp hz⟩
    have h1 : s ≠ 1 := by
      intro h
      have hr : s.re < 1 := r.property.1.2
      simpa [h] using hr
    have hf := Nat.cast_analyticOrderNatAt (zeta_nontrivial_zero_finite_order r).2
    exact ⟨_, (entireXi_order_eq_zeta r.property.1.1 h1).trans hf.symm,
      (zetaCanonicalProduct_order r).trans hf.symm⟩
  · have hn : zetaCanonicalProduct s ≠ 0 := by
      apply zetaCanonicalProduct_ne_zero
      intro r he
      exact hz ((entireXi_eq_zero_iff s).mpr (by rw [he]; exact r.property))
    refine ⟨0, ?_, ?_⟩ <;>
      simp only [Nat.cast_zero] <;> apply analyticOrderAt_eq_zero.mpr <;> right <;> assumption

private theorem quotient_order_zero (s : ℂ) : meromorphicOrderAt xiProductQuotient s = 0 := by
  obtain ⟨n,hx,hp⟩ := xi_product_orders s
  have ha := entireXi_analytic s
  have hb := zetaCanonicalProduct_entire s (Set.mem_univ _)
  rw [xiProductQuotient, meromorphicOrderAt_toMeromorphicNFOn quotient_meromorphic (Set.mem_univ _),
    meromorphicOrderAt_div ha.meromorphicAt hb.meromorphicAt,
    ha.meromorphicOrderAt_eq, hb.meromorphicOrderAt_eq, hx, hp]
  simp

theorem xiProductQuotient_unit (s : ℂ) :
    AnalyticAt ℂ xiProductQuotient s ∧ xiProductQuotient s ≠ 0 := by
  have hn : MeromorphicNFAt xiProductQuotient s :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)
  have ho := quotient_order_zero s
  exact ⟨hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp ho.ge,
    hn.meromorphicOrderAt_eq_zero_iff.mp ho⟩

theorem xiProductQuotient_mul (s : ℂ) : xiProductQuotient s * zetaCanonicalProduct s = entireXi s := by
  by_cases hz : entireXi s = 0
  · let r : NontrivialZetaZero := ⟨s, (entireXi_eq_zero_iff s).mp hz⟩
    have hp : zetaCanonicalProduct s = 0 := zetaCanonicalProduct_zero r
    rw [hp, mul_zero, hz]
  · have hp : zetaCanonicalProduct s ≠ 0 := by
      apply zetaCanonicalProduct_ne_zero
      intro r he
      exact hz ((entireXi_eq_zero_iff s).mpr (by rw [he]; exact r.property))
    have ha := (entireXi_analytic s).div (zetaCanonicalProduct_entire s (Set.mem_univ _)) hp
    rw [xiProductQuotient, toMeromorphicNFOn_eq_toMeromorphicNFAt quotient_meromorphic (Set.mem_univ _),
      toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
    exact div_mul_cancel₀ _ hp

theorem xiProductQuotient_zero : xiProductQuotient 0 = 1 := by
  simpa [zetaCanonicalProduct, zetaFactor, genusOne, entireXi] using xiProductQuotient_mul 0

theorem exists_normalized_entire_log_quotient :
    ∃ G : ℂ → ℂ, (∀ s, AnalyticAt ℂ G s) ∧ G 0 = 0 ∧
      ∀ s, Complex.exp (G s) = xiProductQuotient s := by
  have hU : IsSimplyConnected (Set.univ : Set ℂ) := by
    letI : ContractibleSpace (Set.univ : Set ℂ) :=
      (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
    exact (inferInstance : SimplyConnectedSpace (Set.univ : Set ℂ))
  obtain ⟨g,hg,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    (g := xiProductQuotient) (fun s _ => (xiProductQuotient_unit s).1.continuousAt.continuousWithinAt)
    (fun ⟨s,_,hs⟩ => (xiProductQuotient_unit s).2 hs)
  have heq (s : ℂ) : Complex.exp (g s) = xiProductQuotient s := he (Set.mem_univ s)
  have hga (s : ℂ) : AnalyticAt ℂ g s := by
    have ha : AnalyticAt ℂ Complex.exp (g s) := by fun_prop
    have hd : deriv Complex.exp (g s) ≠ 0 := by simp
    let L := ha.hasStrictDerivAt.localInverse _ _ _ hd
    have hL : AnalyticAt ℂ L (xiProductQuotient s) := by
      rw [← heq s]
      exact ha.analyticAt_localInverse hd
    apply (hL.comp (xiProductQuotient_unit s).1).congr
    have hc := (continuousOn_univ.mp hg).continuousAt (x := s)
    filter_upwards [hc.tendsto.eventually (ha.hasStrictDerivAt.eventually_left_inverse hd)] with t ht
    exact (congrArg L (heq t).symm).trans ht
  refine ⟨fun s => g s-g 0, fun s => (hga s).sub analyticAt_const, sub_self _, ?_⟩
  intro s
  rw [Complex.exp_sub, heq, heq, xiProductQuotient_zero, div_one]

end RHConnections.CanonicalFactor
