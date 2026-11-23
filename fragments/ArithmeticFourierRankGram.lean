import Verified
import SquarefreeIntervalActivity

noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierInversion ArithmeticFourierMertensKernel ArithmeticFourierShell

def actualResidual (N : ℕ) (K : ℕ → ℝ) (n : ℕ) : ℝ :=
  K n-averageCorrection N K n

private theorem actual_residual_add (N : ℕ) (K L : ℕ → ℝ) :
    actualResidual N (K+L) = actualResidual N K+actualResidual N L := by
  funext n
  unfold actualResidual averageCorrection
  simp only [Pi.add_apply]
  split_ifs <;> (try dsimp only [Pi.add_apply]) <;> (try split_ifs) <;> ring

private theorem sqNorm_add (N : ℕ) (U V : ℕ → ℝ) :
    sqNorm N (U+V) = sqNorm N U+sqNorm N V+2*dot N U V := by
  unfold sqNorm dot
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,Pi.add_apply]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem rank_pair_cross_cost (N : ℕ) (K L : ℕ → ℝ) :
    let P := positivePositions N
    let V := negativePositions N
    let k := min P.card V.card
    dot N (actualResidual N K) (actualResidual N L) =
      (∑ i ∈ Finset.range k,
        (K (indexAt P i)-K (indexAt V i))*(L (indexAt P i)-L (indexAt V i)))/2 +
      (∑ i ∈ Finset.Ico k P.card,K (indexAt P i)*L (indexAt P i)) +
      ∑ i ∈ Finset.Ico k V.card,K (indexAt V i)*L (indexAt V i) := by
  have htotal := rank_pair_squared_cost N (K+L)
  have hK := rank_pair_squared_cost N K
  have hL := rank_pair_squared_cost N L
  dsimp only at htotal hK hL ⊢
  change sqNorm N (actualResidual N (K+L)) = _ at htotal
  change sqNorm N (actualResidual N K) = _ at hK
  change sqNorm N (actualResidual N L) = _ at hL
  rw [actual_residual_add,sqNorm_add] at htotal
  have hmain (p m : ℕ) : (((K+L) p-(K+L) m)^2)/2 =
      (K p-K m)^2/2+(L p-L m)^2/2+(K p-K m)*(L p-L m) := by
    simp only [Pi.add_apply]
    ring
  have htail (n : ℕ) : ((K+L) n)^2 = (K n)^2+(L n)^2+2*(K n*L n) := by
    simp only [Pi.add_apply]
    ring
  simp only [hmain,htail,Finset.sum_add_distrib,← Finset.mul_sum] at htotal
  linear_combination (htotal-hK-hL)/2

def prefixCount (S : Finset ℕ) (t : ℕ) : ℕ := (S.filter fun n => n≤t).card

private theorem prefix_count_mono (S : Finset ℕ) : Monotone (prefixCount S) :=
  fun _ _ h => Finset.card_le_card (fun _ hn => by
    obtain ⟨ha,hb⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨ha,hb.trans h⟩)

private theorem prefix_count_le (S : Finset ℕ) (t : ℕ) : prefixCount S t≤S.card :=
  Finset.card_filter_le _ _

private theorem step_index_eq (S : Finset ℕ) (t : ℕ) {i : ℕ} (hi : i<S.card) :
    cutoffStep t (indexAt S i) = RHConnections.CrossingPairing.stepValue i (prefixCount S t) := by
  simp only [cutoffStep,RHConnections.CrossingPairing.stepValue,prefixCount,prefix_membership_of_rank hi]
  rfl

theorem actual_cutoff_gram (N s t : ℕ) (hst : s≤t) :
    let P := positivePositions N
    let V := negativePositions N
    dot N (actualResidual N (cutoffStep s)) (actualResidual N (cutoffStep t)) =
      ((RHConnections.CrossingPairing.crossings P.card V.card (prefixCount P s) (prefixCount V s) ∩
         RHConnections.CrossingPairing.crossings P.card V.card (prefixCount P t) (prefixCount V t)).card:ℝ)/2 +
      RHConnections.CrossingPairing.unmatchedInside P.card V.card (prefixCount P s) (prefixCount V s) := by
  let P := positivePositions N
  let V := negativePositions N
  let k := min P.card V.card
  let f := RHConnections.CrossingPairing.stepValue
  have h := RHConnections.CrossingPairing.cutoff_gram (prefix_count_mono P hst) (prefix_count_mono V hst)
    (prefix_count_le P t) (prefix_count_le V t)
  have hmain : (∑ i ∈ Finset.range k,
      (cutoffStep s (indexAt P i)-cutoffStep s (indexAt V i))*
      (cutoffStep t (indexAt P i)-cutoffStep t (indexAt V i))) =
    ∑ i ∈ Finset.range k,(f i (prefixCount P s)-f i (prefixCount V s))*
      (f i (prefixCount P t)-f i (prefixCount V t)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hp := (Finset.mem_range.mp hi).trans_le (min_le_left P.card V.card)
    have hv := (Finset.mem_range.mp hi).trans_le (min_le_right P.card V.card)
    rw [step_index_eq P s hp,step_index_eq P t hp,step_index_eq V s hv,step_index_eq V t hv]
  have htail (S : Finset ℕ) : (∑ i ∈ Finset.Ico k S.card,
      cutoffStep s (indexAt S i)*cutoffStep t (indexAt S i)) =
      ∑ i ∈ Finset.Ico k S.card, f i (prefixCount S s)*f i (prefixCount S t) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiS := (Finset.mem_Ico.mp hi).2
    rw [step_index_eq S s hiS,step_index_eq S t hiS]
  rw [rank_pair_cross_cost]
  change ((_ : ℝ)/2 + _ + _) = _
  rw [hmain,htail P,htail V]
  exact h

theorem actual_cutoff_gram_zero (N s t : ℕ) (hst : s≤t)
    (hgap :
      max (prefixCount (positivePositions N) s) (prefixCount (negativePositions N) s) ≤
      min (prefixCount (positivePositions N) t) (prefixCount (negativePositions N) t)) :
    dot N (actualResidual N (cutoffStep s)) (actualResidual N (cutoffStep t)) = 0 := by
  rw [actual_cutoff_gram N s t hst,RHConnections.CrossingPairing.separated_crossings hgap,
    RHConnections.CrossingPairing.unmatchedInside_zero (hgap.trans
      (min_le_min (prefix_count_le _ t) (prefix_count_le _ t)))]
  norm_num

private theorem positive_prefix_eq {N t : ℕ} (ht : t≤N) :
    (positivePositions N).filter (fun n => n≤t) = positiveMobius (Finset.Ioc 0 t) := by
  ext n
  simp only [positivePositions,positiveMobius,Finset.mem_filter,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h₀,_⟩,hm⟩,hl⟩
    exact ⟨⟨h₀,hl⟩,hm⟩
  · rintro ⟨⟨h₀,hl⟩,hm⟩
    exact ⟨⟨⟨h₀,hl.trans ht⟩,hm⟩,hl⟩

private theorem negative_prefix_eq {N t : ℕ} (ht : t≤N) :
    (negativePositions N).filter (fun n => n≤t) = negativeMobius (Finset.Ioc 0 t) := by
  ext n
  simp only [negativePositions,negativeMobius,Finset.mem_filter,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h₀,_⟩,hm⟩,hl⟩
    exact ⟨⟨h₀,hl⟩,hm⟩
  · rintro ⟨⟨h₀,hl⟩,hm⟩
    exact ⟨⟨⟨h₀,hl.trans ht⟩,hm⟩,hl⟩

theorem prefix_rank_imbalance {N t : ℕ} (ht : t≤N) :
    ((prefixCount (positivePositions N) t:ℕ):ℝ)-(prefixCount (negativePositions N) t:ℝ)=M t := by
  rw [prefixCount,prefixCount,positive_prefix_eq ht,negative_prefix_eq ht,
    ← signed_sum_count_difference,M]

def nonzeroActivity (t : ℕ) : ℕ := (nonzeroMobius (Finset.Ioc 0 t)).card

theorem prefix_rank_activity {N t : ℕ} (ht : t≤N) :
    prefixCount (positivePositions N) t + prefixCount (negativePositions N) t =
      nonzeroActivity t := by
  rw [prefixCount,prefixCount,positive_prefix_eq ht,negative_prefix_eq ht,
    nonzeroActivity,nonzeroMobius_partition]
  have hd : Disjoint (positiveMobius (Finset.Ioc 0 t)) (negativeMobius (Finset.Ioc 0 t)) := by
    rw [Finset.disjoint_left]
    intro n hp hn
    have h₁ := (Finset.mem_filter.mp hp).2
    have h₂ := (Finset.mem_filter.mp hn).2
    linarith only [h₁,h₂]
  rw [Finset.card_union_of_disjoint hd]

theorem actual_cutoff_gram_zero_of_activity {N s t : ℕ} (hst : s≤t) (ht : t≤N)
    (h : |M s|+|M t| ≤ (nonzeroActivity t:ℝ)-(nonzeroActivity s:ℝ)) :
    dot N (actualResidual N (cutoffStep s)) (actualResidual N (cutoffStep t)) = 0 := by
  let p := prefixCount (positivePositions N) s
  let n := prefixCount (negativePositions N) s
  let q := prefixCount (positivePositions N) t
  let m := prefixCount (negativePositions N) t
  have hs := hst.trans ht
  have ha := prefix_rank_imbalance (N := N) hs
  have hb := prefix_rank_imbalance (N := N) ht
  have hc := prefix_rank_activity (N := N) hs
  have hd := prefix_rank_activity (N := N) ht
  rw [← ha,← hb,← hc,← hd,Nat.cast_add,Nat.cast_add] at h
  have hh : |(p:ℤ)-n|+|(q:ℤ)-m|≤(q:ℤ)+m-p-n := by
    push_cast
    exact_mod_cast (show |(p:ℝ)-n|+|(q:ℝ)-m|≤(q:ℝ)+m-p-n by
      change |(p:ℝ)-n|+|(q:ℝ)-m|≤((q:ℝ)+m)-p-n
      linarith only [h])
  exact actual_cutoff_gram_zero N s t hst (RHConnections.CrossingPairing.separation_iff_activity.mpr hh)

theorem nonzero_activity_interval {s t : ℕ} (hst : s≤t) :
    (nonzeroActivity t:ℝ)-(nonzeroActivity s:ℝ) =
      (((Finset.Ioc s t).filter Squarefree).card:ℝ) := by
  have hsf (n : ℕ) : muR n≠0 ↔ Squarefree n := by
    change (ArithmeticFunction.moebius n:ℝ)≠0 ↔ Squarefree n
    rw [Int.cast_ne_zero,ArithmeticFunction.moebius_ne_zero_iff_squarefree]
  have he (u : ℕ) : nonzeroMobius (Finset.Ioc 0 u) = (Finset.Ioc 0 u).filter Squarefree := by
    ext n
    simp only [nonzeroMobius,Finset.mem_filter,hsf]
  have hsub : (Finset.Ioc (0:ℕ) s).filter Squarefree ⊆ (Finset.Ioc 0 t).filter Squarefree := by
    intro n hn
    obtain ⟨hsupport,hQ⟩ := Finset.mem_filter.mp hn
    obtain ⟨h0,hs⟩ := Finset.mem_Ioc.mp hsupport
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h0,hs.trans hst⟩,hQ⟩
  have hdiff : (Finset.Ioc (0:ℕ) t).filter Squarefree \ (Finset.Ioc 0 s).filter Squarefree =
      (Finset.Ioc s t).filter Squarefree := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hn0,hnt⟩,hsq⟩,hnot⟩
      exact ⟨⟨by by_contra! h; exact hnot ⟨⟨hn0,h⟩,hsq⟩,hnt⟩,hsq⟩
    · rintro ⟨⟨hns,hnt⟩,hsq⟩
      exact ⟨⟨⟨(Nat.zero_le s).trans_lt hns,hnt⟩,hsq⟩,fun h => (not_le_of_gt hns) h.1.2⟩
  have hcard := Finset.card_sdiff_of_subset hsub
  rw [hdiff] at hcard
  simp only [nonzeroActivity,he]
  rw [← Nat.cast_sub (Finset.card_le_card hsub),← hcard]

theorem actual_cutoff_gram_zero_of_spacing {N s t : ℕ} (hst : s≤t) (ht : t≤N) {B : ℝ}
    (hsB : |M s|≤B) (htB : |M t|≤B)
    (hgap : 8*B + 4*(N.sqrt:ℝ) ≤ ((t-s:ℕ):ℝ)) :
    dot N (actualResidual N (cutoffStep s)) (actualResidual N (cutoffStep t)) = 0 := by
  apply actual_cutoff_gram_zero_of_activity hst ht
  rw [nonzero_activity_interval hst]
  have hsq := squarefree_interval_card_lower s t hst
  have hn : (t.sqrt:ℝ) ≤ N.sqrt := by exact_mod_cast
    (Nat.le_sqrt.mpr ((Nat.sqrt_le t).trans ht))
  linarith only [hsB,htB,hgap,hsq,hn]

end RHConnections.RankPairing
