import Verified
import Mathlib.Topology.Order.Compact

namespace RHConnections.AnalyticObligations

theorem compact_parameter_gap {a : ℝ} {z₀ : ℂ} (hz₀ : a < z₀.re)
    {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ halfPlane a) :
    ∃ beta L : ℝ, a < beta ∧ 0 ≤ L ∧ beta ≤ z₀.re ∧ ‖z₀‖ ≤ L ∧
      ∀ z ∈ K, beta ≤ z.re ∧ ‖z‖ ≤ L := by
  let S : Set ℂ := insert z₀ K
  have hS : IsCompact S := hK.insert z₀
  have hne : S.Nonempty := ⟨z₀, Set.mem_insert _ _⟩
  obtain ⟨m, hm, hmin⟩ := hS.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨q, hq, hmax⟩ := hS.exists_isMaxOn hne continuous_norm.continuousOn
  have ham : a < m.re := by
    rcases hm with hm | hm
    · simpa only [hm] using hz₀
    · exact hsub hm
  have hmid : a < (a + m.re)/2 := by linarith
  have hle : (a + m.re)/2 ≤ m.re := by linarith
  refine ⟨(a+m.re)/2, ‖q‖, hmid, norm_nonneg q,
    hle.trans (hmin (Set.mem_insert _ _)), hmax (Set.mem_insert _ _), ?_⟩
  intro z hz
  exact ⟨hle.trans (hmin (Set.mem_insert_of_mem _ hz)),
    hmax (Set.mem_insert_of_mem _ hz)⟩

end RHConnections.AnalyticObligations
