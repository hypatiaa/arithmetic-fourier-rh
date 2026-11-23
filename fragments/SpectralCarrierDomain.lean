import Verified
import Mathlib.Analysis.Normed.Module.Connected

open Filter
namespace RHConnections.SpectralTail

theorem range_closed_of_radially_finite {ι : Type*} (rho : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖rho i‖ ≤ R}.Finite) : IsClosed (Set.range rho) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  let J : Set ι := {i | ‖rho i‖ ≤ ‖s‖+1}
  have hJ : (rho '' J).Finite := (hfinite _).image rho
  have hsJ : s ∈ (rho '' J)ᶜ := by
    intro h
    obtain ⟨i,_,hi⟩ := h
    exact hs ⟨i,hi⟩
  have hop := hJ.isClosed.isOpen_compl
  apply mem_of_superset (inter_mem (hop.mem_nhds hsJ) (Metric.ball_mem_nhds s zero_lt_one))
  intro t ht
  rintro ⟨i,rfl⟩
  apply ht.1
  refine ⟨i,?_ ,rfl⟩
  change ‖rho i‖ ≤ ‖s‖+1
  have hdist : ‖rho i-s‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using ht.2
  calc
    _ = ‖rho i-s+s‖ := by rw [sub_add_cancel]
    _ ≤ ‖rho i-s‖+‖s‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem range_countable_of_radially_finite {ι : Type*} (rho : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖rho i‖ ≤ R}.Finite) : (Set.range rho).Countable := by
  have hcover : Set.range rho = ⋃ n : ℕ, rho '' {i | ‖rho i‖ ≤ (n:ℝ)} := by
    ext s
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨n,hn⟩ := exists_nat_gt ‖rho i‖
      exact Set.mem_iUnion.mpr ⟨n, i, hn.le, rfl⟩
    · intro h
      obtain ⟨n,i,_,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨i,hi⟩
  rw [hcover]
  exact Set.countable_iUnion (fun n => ((hfinite n).image rho).countable)

theorem complement_connected_of_radially_finite {ι : Type*} (rho : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖rho i‖ ≤ R}.Finite) :
    IsConnected (Set.range rho)ᶜ :=
  (range_countable_of_radially_finite rho hfinite).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)

end RHConnections.SpectralTail
