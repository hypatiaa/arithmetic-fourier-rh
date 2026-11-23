import Verified

noncomputable section
open Filter
namespace RHConnections.RankContrast

theorem nominalQ_nat_atTop {eta : ℝ} (he : 0<eta) (he1 : eta<1) :
    Tendsto (fun t : ℕ => nominalQ eta (t:ℝ)) atTop atTop := by
  have hlin : Tendsto (fun t : ℕ => 3*(t:ℝ)/2) atTop atTop := by
    apply tendsto_atTop_mono' _ _ tendsto_natCast_atTop_atTop
    filter_upwards with t
    linarith [Nat.cast_nonneg (α := ℝ) t]
  exact (tendsto_rpow_atTop he).comp ((tendsto_rpow_atTop (inv_pos.mpr (sub_pos.mpr he1))).comp hlin)

theorem eventually_log_rpow_absorbed (A : ℝ) {s : ℝ} (hs : 0<s) :
    ∀ᶠ q : ℝ in atTop, (Real.log q)^A ≤ q^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop A hs).bound
    (by norm_num : (0:ℝ)<1),eventually_ge_atTop (1:ℝ)] with q h hq
  simpa [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hq) A),
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hq) s)] using h

theorem normalized_excursion_lower {eta t m b : ℝ}
    (he : 0<eta) (he1 : eta<1) (ht : 0<t) (hb : b≤1) (hm : t^b≤m) :
    (nominalQ eta t)^(-((1-eta)/eta)*(1-b)) ≤ m/t := by
  let q := nominalQ eta t
  let l := (1-eta)/eta
  have hq : 0<q := by dsimp [q,nominalQ,nominalX]; positivity
  have hqt : t≤q^l := by
    have h := central_scale_relation he he1 ht
    change t=(2/3)*q^l at h
    linarith [Real.rpow_pos_of_pos hq l]
  have h := Real.rpow_le_rpow_of_nonpos ht hqt (show b-1≤0 by linarith)
  rw [←Real.rpow_mul hq.le] at h
  change q^(-l*(1-b)) ≤ m/t
  rw [show -l*(1-b)=l*(b-1) by ring]
  refine h.trans ?_
  rwa [Real.rpow_sub ht,Real.rpow_one,div_le_div_iff_of_pos_right ht]

theorem eventually_strict_power_domination (C : ℝ) {a b : ℝ} (hab : a<b) :
    ∀ᶠ q : ℝ in atTop, C*q^a<q^b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_gt_atTop C,
    eventually_gt_atTop (0:ℝ)] with q h hq
  change C<q^(b-a) at h
  rwa [Real.rpow_sub hq,lt_div_iff₀ (Real.rpow_pos_of_pos hq a)] at h

theorem eventual_rank_excursion_thresholds {eta b : ℝ}
    (he : 0<eta) (he1 : eta<1) (hb : 0<b) (hb1 : b≤1)
    (hgap : ((1-eta)/eta)*(1-b)<1/8) (height : ℝ) :
    ∀ᶠ t : ℕ in atTop, ∀ m : ℕ, (t:ℝ)^b≤m →
      let q := nominalQ eta (t:ℝ)
      1<q ∧ 2*q^(1/8:ℝ)≤q^(1/6:ℝ) ∧ height<q^(1/8:ℝ) ∧
      8≤m ∧ 20*q^(-(1/8:ℝ))<(m:ℝ)/t ∧
      q^(-((1-eta)/eta)*(1-b))≤(m:ℝ)/t := by
  have hq := nominalQ_nat_atTop he he1
  filter_upwards [hq.eventually_gt_atTop 1,
    hq.eventually (eventually_strict_power_domination 2 (by norm_num : (1/8:ℝ)<1/6)),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp hq).eventually_gt_atTop height,
    ((tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (8:ℝ),
    hq.eventually (eventually_strict_power_domination 20
      (show -(1/8:ℝ)< -((1-eta)/eta)*(1-b) by linarith)),
    eventually_gt_atTop (0:ℕ)] with t h1 h2 h3 h4 h5 ht
  intro m hm
  have hn := normalized_excursion_lower he he1 (by exact_mod_cast ht : (0:ℝ)<t) hb1 hm
  exact ⟨h1,h2.le,h3,by exact_mod_cast h4.trans hm,h5.trans_le hn,hn⟩

end RHConnections.RankContrast
