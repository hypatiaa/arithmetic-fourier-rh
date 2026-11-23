import Verified
import BlockCutoffIntervals
import BlockJacksonMoment

noncomputable section
namespace RHConnections.BlockFourier
open RHConnections.RankPairing ArithmeticFourierShell ArithmeticFourierMertensKernel
  ArithmeticFourierInversion

variable {J : ℕ} [NeZero J]

private theorem sum_of_sign_position_counts (N : ℕ) :
    (positivePositions N).card+(negativePositions N).card≤N := by
  let P := positivePositions N
  let V := negativePositions N
  have hd : Disjoint P V := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have h1 := (Finset.mem_filter.mp hn).2
    have h2 := (Finset.mem_filter.mp hm).2
    linarith only [h1,h2]
  rw [← Finset.card_union_of_disjoint hd,← Nat.sub_zero N,← Nat.card_Ioc]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))

theorem rank_residual_of_interval_bound (N : ℕ) (t : ℕ → ℕ) (ht : Antitone t)
    (d : ZMod J → ℝ) (B : ℝ) (hB : 0≤B)
    (h : ∀ a ℓ, ℓ≤J → |blockIntervalSum d a ℓ|≤B) :
    ‖residualVector N (blockCutoffKernel d t)‖ ≤ Real.sqrt (N:ℝ)*B := by
  let P := positivePositions N
  let V := negativePositions N
  let k := min P.card V.card
  let K := blockCutoffKernel d t
  have hlen (n : ℕ) : blockActiveLength J t n≤J := by
    unfold blockActiveLength
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range J)
  have h0 (n : ℕ) : |K n|≤B := by
    dsimp [K]
    rw [block_cutoff_kernel_eq_interval d t ht n]
    exact h _ _ (hlen n)
  have hP (a b : ℕ) : |K a-K b|≤B := by
    dsimp [K]
    rw [block_cutoff_kernel_abs_sub d t ht a b]
    exact h _ _ ((Nat.sub_le ..).trans (max_le (hlen a) (hlen b)))
  have ha : k≤P.card := min_le_left _ _
  have hb : k≤V.card := min_le_right _ _
  have hsq : sqNorm N (fun n => K n-averageCorrection N K n) ≤ (N:ℝ)*B^2 := by
    have hcost := rank_pair_squared_cost N K
    dsimp only at hcost
    rw [hcost]
    have hmain : (∑ i ∈ Finset.range k,(K (indexAt P i)-K (indexAt V i))^2/2) ≤
        (k:ℝ)*B^2/2 := by
      calc
        _ ≤ ∑ _i ∈ Finset.range k,B^2/2 := by
          refine Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_right ?_ (by norm_num))
          rw [← sq_abs (K (indexAt P i)-K (indexAt V i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hP _ _) _
        _ = _ := by simp [div_eq_mul_inv,mul_assoc]
    have ht (S : Finset ℕ) : (∑ i ∈ Finset.Ico k S.card,(K (indexAt S i))^2) ≤
        ((S.card-k:ℕ):ℝ)*B^2 := by
      calc
        _ ≤ ∑ _i ∈ Finset.Ico k S.card,B^2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [← sq_abs (K (indexAt S i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (h0 _) _
        _ = _ := by simp [Nat.card_Ico]
    have hcount : ((k:ℝ)/2)+((P.card-k:ℕ):ℝ)+((V.card-k:ℕ):ℝ) ≤ (N:ℝ) := by
      rw [Nat.cast_sub ha,Nat.cast_sub hb]
      have h := sum_of_sign_position_counts N
      have hr : (P.card:ℝ)+(V.card:ℝ)≤N := by exact_mod_cast h
      linarith only [hr,show (0:ℝ)≤k by positivity]
    change (∑ i ∈ Finset.range k,(K (indexAt P i)-K (indexAt V i))^2/2) +
      (∑ i ∈ Finset.Ico k P.card,(K (indexAt P i))^2) +
      (∑ i ∈ Finset.Ico k V.card,(K (indexAt V i))^2) ≤ _
    calc
      _ ≤ (k:ℝ)*B^2/2+((P.card-k:ℕ):ℝ)*B^2+((V.card-k:ℕ):ℝ)*B^2 :=
        add_le_add (add_le_add hmain (ht P)) (ht V)
      _ = (((k:ℝ)/2)+((P.card-k:ℕ):ℝ)+((V.card-k:ℕ):ℝ))*B^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
  rw [norm_rank_residual]
  exact (Real.sqrt_le_sqrt hsq).trans_eq (by rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hB])

theorem rank_kernel_jackson_error (N : ℕ) (t : ℕ → ℕ) (ht : Antitone t)
    (d : ZMod J → ℝ) (H : ℝ) (hH : 0≤H) (hd : ∀ x, |d x|≤H)
    (R : ℕ) (hR : 0<R) (hRJ : R≤J) :
    let K := blockCutoffKernel d t
    let Klow := blockCutoffKernel (smoothReal R d) t
    |Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n))-
      Real.sqrt (sqNorm N (fun n => Klow n-averageCorrection N Klow n))| ≤
      6*Real.sqrt (N:ℝ)*H*(J:ℝ)/(R:ℝ) := by
  let K := blockCutoffKernel d t
  let Klow := blockCutoffKernel (smoothReal R d) t
  change |Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n))-
    Real.sqrt (sqNorm N (fun n => Klow n-averageCorrection N Klow n))| ≤ _
  rw [← norm_rank_residual N K,← norm_rank_residual N Klow]
  apply (abs_norm_sub_norm_le _ _).trans
  have hk : K-Klow = blockCutoffKernel (d-smoothReal R d) t := by
    ext n
    simp only [K,Klow,blockCutoffKernel,Pi.sub_apply,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  rw [← map_sub,hk]
  let A := 6*H*(J:ℝ)/(R:ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  have hbound (a : ZMod J) (ℓ : ℕ) : |blockIntervalSum (d-smoothReal R d) a ℓ|≤A := by
    have he := block_interval_smoothing d (smoothingKernel R) H hd (smoothing_kernel_mass hR) a ℓ
    change |blockIntervalSum (d-smoothReal R d) a ℓ|≤
      2*H*∑ h,|smoothingKernel R h| * (blockCyclicDistance h:ℝ) at he
    simp only [abs_of_nonneg (smoothing_kernel_nonneg R _)] at he
    exact (he.trans (mul_le_mul_of_nonneg_left (jackson_circular_first_moment R hR hRJ)
      (by positivity))).trans_eq (by dsimp [A]; ring)
  exact (rank_residual_of_interval_bound N t ht (d-smoothReal R d) A hA (fun a ℓ _ => hbound a ℓ)).trans_eq (by dsimp [A]; ring)

end RHConnections.BlockFourier
