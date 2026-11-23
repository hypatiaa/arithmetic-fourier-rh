import Verified
import BoundedComplexCenter

noncomputable section
open Set
namespace RHConnections.LongRankPhase
open RHConnections.RankPairing RHConnections.BlockFourier RHConnections.RankContrast

theorem long_row_entry_linear_bound (X Q : ℝ) (hQ : 1≤Q) {D : ℝ} (hD : 0≤D)
    (hLip : ∀ a∈Icc Q (2*Q),∀ b∈Icc Q (2*Q),
      ‖rightPotential Q b-rightPotential Q a‖≤D*|b-a|) (r : RankRow) :
    ‖longRowValue X Q r‖≤(D*realDyadicMeshWidth Q)*((rowStartLength X Q r).2:ℝ) := by
  let J := realDyadicMeshCount Q
  let R := realDyadicMeshRadius Q
  let u := realDyadicMeshPoint Q
  let H := realDyadicMeshWidth Q
  obtain ⟨hu,hu0,huJ,hw,_,hR,hRJ,_⟩ := real_dyadic_mesh Q hQ
  have hJ := hR.trans_le hRJ
  letI : NeZero J := ⟨hJ.ne'⟩
  let d : ZMod J → ℂ := shellBlockSignal u (rightPotential Q)
  have hpoint (i : ZMod J) : ‖d i‖≤D*H := by
    have hi := ZMod.val_lt i
    have hdom (j : ℕ) (hj : j≤J) : u j∈Icc Q (2*Q) :=
      ⟨hu0 ▸ hu (Nat.zero_le _),huJ ▸ hu hj⟩
    have h := hLip (u i.val) (hdom _ hi.le) (u (i.val+1)) (hdom _ (Nat.succ_le_of_lt hi))
    rw [abs_of_nonneg (sub_nonneg.mpr (hu (Nat.le_succ _)))] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hw _) hD)
  have hSmooth (j : ZMod J) :
      ‖smoothComplexPositive (smoothingKernel R) d j‖≤D*H := by
    unfold smoothComplexPositive
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i : ZMod J,smoothingKernel R i*(D*H) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (smoothing_kernel_nonneg R i)]
        exact mul_le_mul_of_nonneg_left (hpoint _) (smoothing_kernel_nonneg R i)
      _ = _ := by rw [←Finset.sum_mul,smoothing_kernel_mass hR,one_mul]
  dsimp only [longRowValue]
  rw [dif_pos hJ]
  split_ifs
  · unfold complexIntervalSum
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _i∈Finset.range (rowStartLength X Q r).2,D*H :=
        Finset.sum_le_sum (fun i _ => hSmooth _)
      _ = _ := by simp [H,nsmul_eq_mul,mul_comm]
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg hD (Real.sqrt_nonneg Q)) (Nat.cast_nonneg _)

theorem improve_long_row_center (X Q : ℝ) (hQ : 1≤Q) {D : ℝ} (hD : 0≤D)
    (hLip : ∀ a∈Icc Q (2*Q),∀ b∈Icc Q (2*Q),
      ‖rightPotential Q b-rightPotential Q a‖≤D*|b-a|) (c : ℂ) :
    ∃ c' : ℂ, ‖c'‖≤2*(D*realDyadicMeshWidth Q) ∧ longRowCost X Q c'≤longRowCost X Q c := by
  let N := ⌊X/Q⌋₊
  obtain ⟨c',hc',h⟩ := bounded_complex_center_finset (rankRows N) rowWeight
    (fun r => ((rowStartLength X Q r).2:ℝ)) (longRowValue X Q) (fun r _ => by
      unfold rowWeight; split_ifs <;> norm_num) (fun r _ => by positivity)
    (show 0≤D*realDyadicMeshWidth Q by unfold realDyadicMeshWidth; positivity)
    (fun r _ => long_row_entry_linear_bound X Q hQ hD hLip r) c
  exact ⟨c',hc',Real.sqrt_le_sqrt h⟩

end RHConnections.LongRankPhase
