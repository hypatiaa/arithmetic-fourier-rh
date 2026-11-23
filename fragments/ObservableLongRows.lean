import Verified

noncomputable section
namespace RHConnections.LongRankPhase
open RHConnections.RankPairing

theorem pair_mem_rank_rows {N i : ℕ}
    (hi : i∈Finset.range (min (positivePositions N).card (negativePositions N).card)) :
    (RankRowKind.pair,i)∈rankRows N := by
  unfold rankRows
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,hi⟩))

theorem paired_subfamily_cost_bound (X Q : ℝ) (c : ℂ) (I : Finset ℕ)
    (hI : ∀ i∈I, i∈Finset.range
      (min (positivePositions ⌊X/Q⌋₊).card (negativePositions ⌊X/Q⌋₊).card)) :
    Real.sqrt (∑ i∈I,‖longRowValue X Q (.pair,i) -
      c*((rowStartLength X Q (.pair,i)).2:ℂ)‖^2)≤
      Real.sqrt 2*longRowCost X Q c := by
  let N := ⌊X/Q⌋₊
  let e : ℕ ↪ RankRow := ⟨fun i => (.pair,i),fun i j h => congrArg Prod.snd h⟩
  let normSq (r : RankRow) :=
      ‖longRowValue X Q r-c*((rowStartLength X Q r).2:ℂ)‖^2
  have hsub : I.map e⊆rankRows N := by
    intro r hr
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hr
    exact pair_mem_rank_rows (hI i hi)
  have hsum : (∑ i∈I,normSq (e i))≤2*(∑ r∈rankRows N,rowWeight r*normSq r) := by
    calc
      _ = 2*(∑ r∈I.map e,rowWeight r*normSq r) := by
        rw [Finset.sum_map,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change normSq (e i)=2*(rowWeight (.pair,i)*normSq (e i))
        rw [show rowWeight (.pair,i)=1/2 from rfl]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ =>
          mul_nonneg (by unfold rowWeight; split_ifs <;> norm_num) (sq_nonneg _))) (by norm_num)
  exact (Real.sqrt_le_sqrt hsum).trans_eq (by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]; rfl)

end RHConnections.LongRankPhase
