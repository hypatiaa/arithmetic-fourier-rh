import Verified
import RankPairingCore

open ArithmeticFunction
noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierInversion ArithmeticFourierShell ArithmeticFourierMertensKernel

def positivePositions (N : ℕ) : Finset ℕ := positiveMobius (Finset.Ioc 0 N)

def negativePositions (N : ℕ) : Finset ℕ := negativeMobius (Finset.Ioc 0 N)

def indexAt (S : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i<S.card then (S.orderIsoOfFin rfl ⟨i,hi⟩).val else 0

private theorem index_mem {S : Finset ℕ} {i : ℕ} (hi : i<S.card) : indexAt S i ∈ S := by
  simp only [indexAt,dite_eq_left hi]
  exact (S.orderIsoOfFin rfl ⟨i,hi⟩).property

def rank (S : Finset ℕ) (n : ℕ) (hn : n∈S) : ℕ :=
  ((S.orderIsoOfFin rfl).symm ⟨n,hn⟩).val

private theorem rank_lt {S : Finset ℕ} {n : ℕ} (hn : n∈S) : rank S n hn < S.card :=
  ((S.orderIsoOfFin rfl).symm ⟨n,hn⟩).isLt

private theorem rank_index {S : Finset ℕ} {i : ℕ} (hi : i<S.card) :
    rank S (indexAt S i) (index_mem hi) = i := by
  let e := S.orderIsoOfFin (rfl : S.card=S.card)
  have hv : indexAt S i = (e ⟨i,hi⟩).val := by simp [indexAt,hi,e]
  have h : (⟨indexAt S i,index_mem hi⟩ : ↥S) = e ⟨i,hi⟩ := Subtype.ext hv
  change (e.symm ⟨indexAt S i,index_mem hi⟩).val = i
  rw [h,OrderIso.symm_apply_apply]

private theorem index_rank {S : Finset ℕ} {n : ℕ} (hn : n∈S) :
    indexAt S (rank S n hn) = n := by
  simp only [indexAt,dite_eq_left (rank_lt hn)]
  change (S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨n,hn⟩)).val = n
  rw [OrderIso.apply_symm_apply]

theorem sum_rank (S : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ S,f n) = ∑ i ∈ Finset.range S.card,f (indexAt S i) := by
  rw [Finset.sum_subtype S (fun _ => Iff.rfl),← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (S.orderIsoOfFin rfl).symm.toEquiv
    (fun n : S => f n.val) (fun i : Fin S.card => f (indexAt S i))
    (fun n => (congrArg f (index_rank n.property)).symm)

private theorem pos_neg_disjoint (N : ℕ) : Disjoint (positivePositions N) (negativePositions N) := by
  rw [Finset.disjoint_left]
  intro n hp hn
  have h₁ := (Finset.mem_filter.mp hp).2
  have h₂ := (Finset.mem_filter.mp hn).2
  linarith only [h₁,h₂]

def averageCorrection (N : ℕ) (K : ℕ → ℝ) (n : ℕ) : ℝ :=
  if hp : n∈positivePositions N then
    let i := rank (positivePositions N) n hp
    if i<(negativePositions N).card then (K n+K (indexAt (negativePositions N) i))/2 else 0
  else if hn : n∈negativePositions N then
    let i := rank (negativePositions N) n hn
    if i<(positivePositions N).card then (K (indexAt (positivePositions N) i)+K n)/2 else 0
  else K n

private theorem correction_pos (N : ℕ) (K : ℕ → ℝ) {i : ℕ} (hi : i<(positivePositions N).card) :
    averageCorrection N K (indexAt (positivePositions N) i) =
      if i<(negativePositions N).card then
        (K (indexAt (positivePositions N) i)+K (indexAt (negativePositions N) i))/2 else 0 := by
  rw [averageCorrection,dite_eq_left (index_mem hi)]
  dsimp only
  rw [rank_index hi]

private theorem correction_neg (N : ℕ) (K : ℕ → ℝ) {i : ℕ} (hi : i<(negativePositions N).card) :
    averageCorrection N K (indexAt (negativePositions N) i) =
      if i<(positivePositions N).card then
        (K (indexAt (positivePositions N) i)+K (indexAt (negativePositions N) i))/2 else 0 := by
  have hn := index_mem hi
  have hp : indexAt (negativePositions N) i ∉ positivePositions N :=
    fun hm => (Finset.disjoint_left.mp (pos_neg_disjoint N)) hm hn
  rw [averageCorrection,dite_eq_right hp,dite_eq_left hn]
  dsimp only
  rw [rank_index hi]

private theorem sum_mobius_by_signs (N : ℕ) (G : ℕ → ℝ) :
    dot N muR G = (∑ n ∈ positivePositions N,G n)-(∑ n ∈ negativePositions N,G n) := by
  let T := Finset.Ioc 0 N
  unfold dot
  have hs : (∑ n ∈ nonzeroMobius T,muR n*G n) = ∑ n ∈ T,muR n*G n := by
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnot => ?_)
    have hz : muR n=0 := by
      by_contra! h
      exact hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
    rw [hz,zero_mul]
  change (∑ n ∈ T,muR n*G n) = _
  rw [← hs,nonzeroMobius_partition]
  change (∑ n ∈ positivePositions N ∪ negativePositions N,muR n*G n) = _
  rw [Finset.sum_union (pos_neg_disjoint N)]
  have hp : (∑ n ∈ positivePositions N,muR n*G n) = ∑ n ∈ positivePositions N,G n := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [(Finset.mem_filter.mp hn).2,one_mul]
  have hm : (∑ n ∈ negativePositions N,muR n*G n) = -(∑ n ∈ negativePositions N,G n) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2,neg_one_mul])
  change (∑ n ∈ positivePositions N,muR n*G n)+(∑ n ∈ negativePositions N,muR n*G n) = _
  rw [hp,hm,sub_eq_add_neg]

private theorem sum_paired_side (a b : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range a, if i<b then f i else 0) = ∑ i ∈ Finset.range (min a b),f i := by
  simp only [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

theorem rank_average_mobius_orthogonal (N : ℕ) (K : ℕ → ℝ) :
    dot N muR (averageCorrection N K) = 0 := by
  let P := positivePositions N
  let V := negativePositions N
  let f := fun i => (K (indexAt P i)+K (indexAt V i))/2
  rw [sum_mobius_by_signs,sum_rank P,sum_rank V]
  have hp : (∑ i ∈ Finset.range P.card,averageCorrection N K (indexAt P i)) =
      ∑ i ∈ Finset.range (min P.card V.card),f i := by
    rw [← sum_paired_side]
    exact Finset.sum_congr rfl (fun _ hi => correction_pos N K (Finset.mem_range.mp hi))
  have hn : (∑ i ∈ Finset.range V.card,averageCorrection N K (indexAt V i)) =
      ∑ i ∈ Finset.range (min V.card P.card),f i := by
    rw [← sum_paired_side]
    exact Finset.sum_congr rfl (fun _ hi => correction_neg N K (Finset.mem_range.mp hi))
  change (∑ i ∈ Finset.range P.card,averageCorrection N K (indexAt P i)) -
    (∑ i ∈ Finset.range V.card,averageCorrection N K (indexAt V i)) = _
  rw [hp,hn,min_comm V.card P.card,sub_self]

theorem rank_pair_squared_cost (N : ℕ) (K : ℕ → ℝ) :
    let P := positivePositions N
    let V := negativePositions N
    let k := min P.card V.card
    sqNorm N (fun n => K n-averageCorrection N K n) =
      (∑ i ∈ Finset.range k,(K (indexAt P i)-K (indexAt V i))^2/2) +
      (∑ i ∈ Finset.Ico k P.card,(K (indexAt P i))^2) +
      ∑ i ∈ Finset.Ico k V.card,(K (indexAt V i))^2 := by
  let P := positivePositions N
  let V := negativePositions N
  let k := min P.card V.card
  let D := fun n => K n-averageCorrection N K n
  have hs : (∑ n ∈ nonzeroMobius (Finset.Ioc 0 N),D n*D n) =
      ∑ n ∈ Finset.Ioc 0 N,D n*D n := by
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnot => ?_)
    have hz : muR n=0 := by
      by_contra! h
      exact hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
    have hp : n∉P := by intro h; have he := (Finset.mem_filter.mp h).2; linarith only [he,hz]
    have hm : n∉V := by intro h; have he := (Finset.mem_filter.mp h).2; linarith only [he,hz]
    simp [D,averageCorrection,hp,hm,P,V]
  change sqNorm N D = _
  unfold sqNorm dot
  rw [← hs,nonzeroMobius_partition]
  change (∑ n ∈ P∪V,D n*D n) = _
  rw [Finset.sum_union (pos_neg_disjoint N),sum_rank P,sum_rank V]
  rw [← Finset.sum_range_add_sum_Ico (f := fun i => D (indexAt P i)*D (indexAt P i)) (min_le_left P.card V.card),
    ← Finset.sum_range_add_sum_Ico (f := fun i => D (indexAt V i)*D (indexAt V i)) (min_le_right P.card V.card)]
  have htailP : (∑ i ∈ Finset.Ico k P.card,D (indexAt P i)*D (indexAt P i)) =
      ∑ i ∈ Finset.Ico k P.card,(K (indexAt P i))^2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hi
    have hnot : ¬i<V.card := by
      intro h
      exact (not_lt_of_ge hl) (lt_min hu h)
    dsimp only [D]
    rw [show averageCorrection N K (indexAt P i) = _ from correction_pos N K hu,
      ite_eq_right hnot,sub_zero,pow_two]
  have htailV : (∑ i ∈ Finset.Ico k V.card,D (indexAt V i)*D (indexAt V i)) =
      ∑ i ∈ Finset.Ico k V.card,(K (indexAt V i))^2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hi
    have hnot : ¬i<P.card := by
      intro h
      exact (not_lt_of_ge hl) (lt_min h hu)
    dsimp only [D]
    rw [show averageCorrection N K (indexAt V i) = _ from correction_neg N K hu,
      ite_eq_right hnot,sub_zero,pow_two]
  have hmain :
      (∑ i ∈ Finset.range k,D (indexAt P i)*D (indexAt P i)) +
      (∑ i ∈ Finset.range k,D (indexAt V i)*D (indexAt V i)) =
      ∑ i ∈ Finset.range k,(K (indexAt P i)-K (indexAt V i))^2/2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hp := (Finset.mem_range.mp hi).trans_le (min_le_left P.card V.card)
    have hv := (Finset.mem_range.mp hi).trans_le (min_le_right P.card V.card)
    dsimp only [D]
    rw [show averageCorrection N K (indexAt P i) = _ from correction_pos N K hp,
      show averageCorrection N K (indexAt V i) = _ from correction_neg N K hv,ite_eq_left hp,ite_eq_left hv]
    ring
  change (_+(∑ i ∈ Finset.Ico k P.card,D (indexAt P i)*D (indexAt P i))) +
      (_+(∑ i ∈ Finset.Ico k V.card,D (indexAt V i)*D (indexAt V i))) =
    (∑ i ∈ Finset.range k,(K (indexAt P i)-K (indexAt V i))^2/2) +
      (∑ i ∈ Finset.Ico k P.card,(K (indexAt P i))^2) + ∑ i ∈ Finset.Ico k V.card,(K (indexAt V i))^2
  rw [htailP,htailV]
  linear_combination hmain

private theorem index_monotone {S : Finset ℕ} {i j : ℕ}
    (hi : i<S.card) (hj : j<S.card) (hle : i ≤ j) :
    indexAt S i ≤ indexAt S j := by
  have h := (S.orderIsoOfFin (rfl : S.card=S.card)).monotone
    (show (⟨i,hi⟩:Fin S.card) ≤ ⟨j,hj⟩ from hle)
  exact (show (if h : i<S.card then (S.orderIsoOfFin rfl ⟨i,h⟩).val else 0) ≤ (if h : j<S.card then (S.orderIsoOfFin rfl ⟨j,h⟩).val else 0) by
    rw [dite_eq_left hi,dite_eq_left hj]
    exact h)

theorem prefix_membership_of_rank {S : Finset ℕ} {i t : ℕ} (hi : i<S.card) :
    indexAt S i ≤ t ↔ i < (S.filter fun n => n ≤ t).card := by
  classical
  let A := (Finset.range S.card).filter fun j => indexAt S j ≤ t
  have he : (A.card:ℝ) = ((S.filter fun n => n ≤ t).card:ℝ) := by
    have h := sum_rank S (fun n => if n ≤ t then (1:ℝ) else 0)
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one] at h
    exact h.symm
  have hc : A.card = (S.filter fun n => n ≤ t).card := by exact_mod_cast he
  rw [← hc]
  constructor
  · intro h
    have hsub : Finset.range (i+1) ⊆ A := by
      intro j hj
      have hj' : j ≤ i := by have := Finset.mem_range.mp hj; omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hj'.trans_lt hi),
        (index_monotone (hj'.trans_lt hi) hi hj').trans h⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega
  · intro h
    by_contra! hbad
    have hsub : A ⊆ Finset.range i := by
      intro j hj
      obtain ⟨hx,hy⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_range.mpr
      by_contra! hle
      exact (not_le_of_gt hbad) ((index_monotone hi (Finset.mem_range.mp hx) hle).trans hy)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega

def cutoffStep (t n : ℕ) : ℝ := if n ≤ t then 1 else 0

theorem rank_step_energy_exact (N t : ℕ) :
    let P := positivePositions N
    let V := negativePositions N
    sqNorm N (fun n => cutoffStep t n-averageCorrection N (cutoffStep t) n) =
      RHConnections.CrossingPairing.cutoffEnergy P.card V.card
        (P.filter fun n => n ≤ t).card (V.filter fun n => n ≤ t).card := by
  classical
  let P := positivePositions N
  let V := negativePositions N
  let k := min P.card V.card
  let p := (P.filter fun n => n ≤ t).card
  let v := (V.filter fun n => n ≤ t).card
  have step (S : Finset ℕ) {i : ℕ} (hi : i<S.card) :
      cutoffStep t (indexAt S i) = if i<(S.filter fun n => n ≤ t).card then 1 else 0 := by
    simp only [cutoffStep,prefix_membership_of_rank hi]
  have tails (S : Finset ℕ) (j : ℕ) :
      (∑ i ∈ Finset.Ico j S.card,(cutoffStep t (indexAt S i))^2) =
      ((Finset.Ico j (S.filter fun n => n ≤ t).card).card:ℝ) := by
    have hfilter : ((Finset.Ico j S.card).filter (fun i => i<(S.filter fun n => n ≤ t).card)) =
        Finset.Ico j (S.filter fun n => n ≤ t).card := by
      have hcard := Finset.card_le_card (Finset.filter_subset (fun n => n ≤ t) S)
      ext i
      simp only [Finset.mem_filter,Finset.mem_Ico]
      omega
    calc
      _ = ∑ i ∈ Finset.Ico j S.card, if i<(S.filter fun n => n ≤ t).card then (1:ℝ) else 0 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [step S (Finset.mem_Ico.mp hi).2]
        split_ifs <;> norm_num
      _ = _ := by rw [← Finset.sum_filter,hfilter]; simp
  have hcross : (∑ i ∈ Finset.range k,
       (cutoffStep t (indexAt P i)-cutoffStep t (indexAt V i))^2/2) =
       ((RHConnections.CrossingPairing.crossings P.card V.card p v).card:ℝ)/2 := by
    have hfilter : ((Finset.range k).filter (fun i => (i<p ∧ v ≤ i) ∨ (i<v ∧ p ≤ i))) =
        RHConnections.CrossingPairing.crossings P.card V.card p v := by
      ext i
      rw [Finset.mem_filter,Finset.mem_range,RHConnections.CrossingPairing.mem_crossings]
    calc
      _ = ∑ i ∈ Finset.range k, if (i<p ∧ v ≤ i) ∨ (i<v ∧ p ≤ i) then (1:ℝ)/2 else 0 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hk := Finset.mem_range.mp hi
        rw [step P (hk.trans_le (min_le_left _ _)),step V (hk.trans_le (min_le_right _ _))]
        exact RHConnections.CrossingPairing.pair_step_residual_sq i p v
      _ = _ := by rw [← Finset.sum_filter,hfilter]; simp [div_eq_mul_inv]
  rw [rank_pair_squared_cost]
  change (∑ i ∈ Finset.range k,(cutoffStep t (indexAt P i)-cutoffStep t (indexAt V i))^2/2) +
      (∑ i ∈ Finset.Ico k P.card,(cutoffStep t (indexAt P i))^2) +
      (∑ i ∈ Finset.Ico k V.card,(cutoffStep t (indexAt V i))^2) =
      RHConnections.CrossingPairing.cutoffEnergy P.card V.card p v
  rw [hcross,tails P,tails V]
  simp only [RHConnections.CrossingPairing.cutoffEnergy,RHConnections.CrossingPairing.unmatchedInside,Nat.cast_add]
  ring

theorem rank_step_cost_le_mertens (N t : ℕ) (ht : t ≤ N) :
    sqNorm N (fun n => cutoffStep t n-averageCorrection N (cutoffStep t) n) ≤ |M t| := by
  rw [rank_step_energy_exact]
  have hp : (positivePositions N).filter (fun n => n ≤ t) = positiveMobius (Finset.Ioc 0 t) := by
    ext n
    simp only [positivePositions,positiveMobius,Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h₀,_⟩,hm⟩,hl⟩
      exact ⟨⟨h₀,hl⟩,hm⟩
    · rintro ⟨⟨h₀,hl⟩,hm⟩
      exact ⟨⟨⟨h₀,hl.trans ht⟩,hm⟩,hl⟩
  have hv : (negativePositions N).filter (fun n => n ≤ t) = negativeMobius (Finset.Ioc 0 t) := by
    ext n
    simp only [negativePositions,negativeMobius,Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h₀,_⟩,hm⟩,hl⟩
      exact ⟨⟨h₀,hl⟩,hm⟩
    · rintro ⟨⟨h₀,hl⟩,hm⟩
      exact ⟨⟨⟨h₀,hl.trans ht⟩,hm⟩,hl⟩
  have h := RHConnections.CrossingPairing.cutoff_energy_le (Finset.filter_subset _ _ |> Finset.card_le_card :
      ((positivePositions N).filter fun n => n ≤ t).card ≤ (positivePositions N).card)
    (Finset.card_le_card (Finset.filter_subset (fun n => n ≤ t) (negativePositions N)))
  rw [hp,hv]
  rwa [hp,hv,← signed_sum_count_difference] at h

end RHConnections.RankPairing
