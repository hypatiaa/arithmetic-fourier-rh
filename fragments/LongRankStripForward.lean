import Verified

noncomputable section
open Filter Set
namespace RHConnections.LongRankPhase
open RHConnections.RankPairing RHConnections.BlockFourier
open RHConnections.PhaseWindow RHConnections.LocalModeContrast

theorem nonnegative_row_weight (r : RankRow) : 0≤rowWeight r := by
  unfold rowWeight
  split_ifs <;> norm_num

theorem rank_rows_weight_sum_le (N : ℕ) : (∑ r∈rankRows N,rowWeight r)≤(N:ℝ) := by
  classical
  let P := positivePositions N
  let V := negativePositions N
  let k := min P.card V.card
  let F := ({RankRowKind.pair} : Finset RankRowKind) ×ˢ Finset.range k
  let G := ({RankRowKind.positive} : Finset RankRowKind) ×ˢ Finset.Ico k P.card
  let H := ({RankRowKind.negative} : Finset RankRowKind) ×ˢ Finset.Ico k V.card
  have tagF (r : RankRow) (hr : r∈F) : r.1=RankRowKind.pair :=
    Finset.mem_singleton.mp (Finset.mem_product.mp hr).1
  have tagG (r : RankRow) (hr : r∈G) : r.1=RankRowKind.positive :=
    Finset.mem_singleton.mp (Finset.mem_product.mp hr).1
  have tagH (r : RankRow) (hr : r∈H) : r.1=RankRowKind.negative :=
    Finset.mem_singleton.mp (Finset.mem_product.mp hr).1
  have hFG : Disjoint F G := Finset.disjoint_left.mpr (fun r hf hg =>
    by have h := (tagF r hf).symm.trans (tagG r hg); cases h)
  have hH : Disjoint (F∪G) H := Finset.disjoint_left.mpr (fun r hfg hh => by
    rcases Finset.mem_union.mp hfg with hf | hg
    · have h := (tagF r hf).symm.trans (tagH r hh)
      cases h
    · have h := (tagG r hg).symm.trans (tagH r hh)
      cases h)
  have hFv : (∑ r∈F,rowWeight r)=(k:ℝ)/2 := by
    have he (r : RankRow) (hr : r∈F) : rowWeight r=1/2 := by
      have hfst := (Finset.mem_product.mp hr).1
      have eq : r.1=RankRowKind.pair := Finset.mem_singleton.mp hfst
      simp [rowWeight,eq]
    rw [Finset.sum_congr rfl he]
    simp [F,Finset.card_product,nsmul_eq_mul,div_eq_mul_inv]
  have hGv : (∑ r∈G,rowWeight r)=((P.card-k:ℕ):ℝ) := by
    have he (r : RankRow) (hr : r∈G) : rowWeight r=1 := by
      have hfst := (Finset.mem_product.mp hr).1
      have eq : r.1=RankRowKind.positive := Finset.mem_singleton.mp hfst
      simp [rowWeight,eq]
    rw [Finset.sum_congr rfl he]
    simp [G,Finset.card_product,nsmul_eq_mul,Nat.card_Ico]
  have hHv : (∑ r∈H,rowWeight r)=((V.card-k:ℕ):ℝ) := by
    have he (r : RankRow) (hr : r∈H) : rowWeight r=1 := by
      have hfst := (Finset.mem_product.mp hr).1
      have eq : r.1=RankRowKind.negative := Finset.mem_singleton.mp hfst
      simp [rowWeight,eq]
    rw [Finset.sum_congr rfl he]
    simp [H,Finset.card_product,nsmul_eq_mul,Nat.card_Ico]
  have hd : Disjoint P V := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have hp := (Finset.mem_filter.mp hn).2
    have hv := (Finset.mem_filter.mp hm).2
    linarith
  have hc : (P.card:ℝ)+(V.card:ℝ)≤N := by
    have hh : P.card+V.card≤N := by
      rw [←Finset.card_union_of_disjoint hd,←Nat.sub_zero N,←Nat.card_Ioc]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    exact_mod_cast hh
  change (∑ r∈F∪G∪H,rowWeight r)≤_
  rw [Finset.sum_union hH,Finset.sum_union hFG,hFv,hGv,hHv,
    Nat.cast_sub (min_le_left P.card V.card),Nat.cast_sub (min_le_right P.card V.card)]
  linarith only [hc,Nat.cast_nonneg (α := ℝ) k]

theorem right_potential_difference_bound {Q k B : ℝ} (hQ : 1≤Q) (hB : 0≤B)
    (hInv : ∀ s : Finset RightZero,
      (∑ r∈s,(rightMultiplicity r:ℝ)/ |(rightValue r).im|)≤B)
    (hStrip : ∀ r : RightZero,(rightValue r).re≤1-k)
    {a b : ℝ} (ha : a∈Icc Q (2*Q)) (hb : b∈Icc Q (2*Q)) :
    ‖rightPotential Q b-rightPotential Q a‖≤4*B*Q^(1-k) := by
  let s := rightHeightFinset (Q^(1/8:ℝ))
  have hQ0 : 0<Q := zero_lt_one.trans_le hQ
  change ‖finiteZeroPotential s rightValue zeroMultiplicity b-
    finiteZeroPotential s rightValue zeroMultiplicity a‖≤_
  unfold finiteZeroPotential
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ r∈s,(4*Q^(1-k))*((rightMultiplicity r:ℝ)/ |(rightValue r).im|) := by
      apply Finset.sum_le_sum
      intro r _
      have hreal : 0<(rightValue r).re := r.val.property.1.1
      have him := abs_pos.mpr (right_zero_nonzero_ordinate r)
      have hi := zero_interval_height_bound hreal.le r.val.property.1.2.le hQ0 ha hb him
      have hm : 0≤zeroMultiplicity r := by unfold zeroMultiplicity; positivity
      rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
      refine (mul_le_mul_of_nonneg_left hi hm).trans ?_
      have hp := Real.rpow_le_rpow_of_exponent_le hQ (hStrip r)
      have hmul : (4:ℝ)*Q^((rightValue r).re) ≤ 4*Q^(1-k) :=
        mul_le_mul_of_nonneg_left hp (by norm_num)
      exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmul him.le) hm).trans_eq (by
        change (rightMultiplicity r:ℝ)*(4*Q^(1-k)/ |(rightValue r).im|)=_
        ring)
    _ = (4*Q^(1-k))*(∑ r∈s,(rightMultiplicity r:ℝ)/ |(rightValue r).im|) := (Finset.mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (hInv s) (by positivity)).trans_eq (by ring)

theorem right_strip_bounds_long_rows (hIngham : ZetaDensityPremise)
    {eta k : ℝ} (he : 0<eta) (hStrip : ∀ r : RightZero,(rightValue r).re≤1-k) :
    UniformLongRowPower eta k := by
  obtain ⟨B,hB,hInv⟩ := right_finite_of_bounded_weighted_inverse_heights hIngham
  refine ⟨8*B,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  refine ⟨0,?_⟩
  let Q := X^eta
  let J := realDyadicMeshCount Q
  let R := realDyadicMeshRadius Q
  let u := realDyadicMeshPoint Q
  let d : ZMod J → ℂ := shellBlockSignal u (rightPotential Q)
  let N := ⌊X/Q⌋₊
  let bound := 8*B*Q^(1-k)
  have hQ : 1≤Q := Real.one_le_rpow hX he.le
  obtain ⟨hu,hu0,huJ,_,_,hR,hRJ,_⟩ := real_dyadic_mesh Q hQ
  have hJ : 0<J := hR.trans_le hRJ
  letI : NeZero J := ⟨hJ.ne'⟩
  have hBound : 0≤bound := by dsimp [bound]; positivity
  have hPd (x : ZMod J) (len : ℕ) (hlen : len≤J) :
      ‖complexIntervalSum d x len‖≤bound := by
    have hh := complex_cyclic_potential_bound d (fun j => rightPotential Q (u j))
      (fun j hj => shell_signal_at_nat u _ hj)
      (show 0≤4*B*Q^(1-k) by positivity)
      (fun j hj l hl => right_potential_difference_bound hQ hB hInv hStrip
        (show u l∈Icc Q (2*Q) by
          exact ⟨hu0 ▸ hu (Nat.zero_le l),huJ ▸ hu hl⟩)
        (show u j∈Icc Q (2*Q) by
          exact ⟨hu0 ▸ hu (Nat.zero_le j),huJ ▸ hu hj⟩)) x len hlen
    exact hh.trans_eq (by dsimp [bound]; ring)
  have hRow (r : RankRow) : ‖longRowValue X Q r‖≤bound := by
    dsimp only [longRowValue]
    rw [dif_pos hJ]
    split_ifs
    · have hl : (rowStartLength X Q r).2≤J := by
        unfold rowStartLength
        dsimp only
        apply (Nat.sub_le ..).trans
        unfold realActiveLength
        exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
      exact complex_cyclic_bound_preserved d (smoothingKernel R) (smoothing_kernel_nonneg R)
        (smoothing_kernel_mass hR) hPd _ _ hl
    · simpa only [norm_zero] using hBound
  change longRowCost X Q 0≤_
  unfold longRowCost
  simp only [zero_mul,sub_zero]
  have hSum : (∑ r∈rankRows N,rowWeight r*‖longRowValue X Q r‖^2)≤(N:ℝ)*bound^2 := by
    calc
      _ ≤ ∑ r∈rankRows N,rowWeight r*bound^2 := by
        apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hRow r) _)
          (nonnegative_row_weight r)
      _ = (∑ r∈rankRows N,rowWeight r)*bound^2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (rank_rows_weight_sum_le N) (sq_nonneg _)
  exact (Real.sqrt_le_sqrt hSum).trans_eq (by
    rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hBound]
    dsimp [bound,Q,N]
    ring)

end RHConnections.LongRankPhase
