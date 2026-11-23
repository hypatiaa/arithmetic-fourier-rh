import Verified
import LongRankStripForward
import ActualSampledRankWindow
import IntegerWindowObserver
import RankStripAsymptotics
import WindowUniformObserver
import WindowCostAlgebra

noncomputable section
open Set Filter
namespace RHConnections.LongRankPhase
open RHConnections.PhaseWindow RHConnections.RankContrast
open RHConnections.MobiusCrossingLengths RHConnections.MertensCriterion

theorem uniform_natural_long_row_power_forces_strip (hIngham : ZetaDensityPremise)
    {eta delta : ℝ} (he : 0<eta) (he1 : eta<1)
    (hd : 0<delta) (hd1 : delta≤1/8) (hPower : UniformNaturalLongRowPower eta delta)
    {s : ℂ} (hs : 1-delta/(1+(5/2)*((1-eta)/eta))<s.re) :
    riemannZeta s≠0 := by
  intro hz
  let lambda := (1-eta)/eta
  have hLambda : 0<lambda := div_pos (sub_pos.mpr he1) he
  have hden : 0<1+(5/2)*lambda := by positivity
  have hδdiv : delta/(1+(5/2)*lambda)≤1/8 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hsR : 7/8<s.re := by linarith
  have hs0 : 0<s.re := by linarith
  have hs1 : s.re<1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
  let target : RightZero := ⟨⟨s,⟨⟨hs0,hs1⟩,hz⟩⟩,hsR⟩
  obtain ⟨d,e,_,hdsub,hd8,he0,heβ,hshort,hExp⟩ :=
    choose_strip_obstruction_parameters hLambda hs0 hs1 hd hd1 hs
  let b := s.re-e
  let a := -lambda*(1-b)
  have hb : 0<b := sub_pos.mpr heβ
  have hbβ : b<s.re := sub_lt_self _ he0
  have hb1 : b<1 := hbβ.trans hs1
  have hgap : ((1-eta)/eta)*(1-b)<1/8 := by
    change lambda*(1-b)<1/8
    convert hshort using 1 <;> dsimp [b] <;> ring
  have hExp' : 1-d<s.re+a*(5/2) := by
    convert hExp using 1 <;> dsimp [a,b] <;> ring
  let W := Real.log (13/12)
  have hW : 0<W := Real.log_pos (by norm_num)
  have hW' : W<Real.log (7/6) := Real.log_lt_log (by norm_num) (by norm_num)
  obtain ⟨C,hC,T,hWin⟩ := actual_sampled_rank_window_inequality hIngham he he1 target hW hW'.le
  obtain ⟨B,hB,S,hObs⟩ :=
    natural_power_observes_sample_windows he he1 hdsub.le (by linarith) hd.le hW' hPower
  let K := ‖s-1‖/8
  have hK : 0<K := by
    have hn : s-1≠0 := sub_ne_zero.mpr (by
      intro h
      rw [h,Complex.one_re] at hs1
      exact (lt_irrefl _ hs1))
    exact div_pos (norm_pos_iff.mpr hn) (by norm_num)
  let D := C*(B+1)
  have hD : 0≤D := by dsimp [D]; positivity
  have hQ := nominalQ_nat_atTop he he1
  have hError : ∀ᶠ q : ℝ in atTop, q^(7/8:ℝ)*(Real.log q)^5≤q^(1-d) := by
    filter_upwards [eventually_log_rpow_absorbed 5 (show 0<1/8-d by linarith),
      eventually_gt_atTop (0:ℝ)] with q hlog hq
    have hlog' : (Real.log q)^ (5:ℕ) ≤ q^(1/8-d) := by
      change (Real.log q)^(5:ℝ)≤q^(1/8-d) at hlog
      have hFive : (5:ℝ) = ((5:ℕ):ℝ) := by norm_num
      rw [hFive,Real.rpow_natCast] at hlog
      exact hlog
    exact (mul_le_mul_of_nonneg_left hlog' (Real.rpow_nonneg hq.le _)).trans_eq
      (by rw [←Real.rpow_add hq]; congr 1; ring)
  have hThresholds := eventual_rank_excursion_thresholds he he1 hb hb1.le hgap |s.im|
  have hAll : ∀ᶠ t : ℕ in atTop,
      (∀ m : ℕ, (t:ℝ)^b≤m →
        let q := nominalQ eta (t:ℝ)
        1<q ∧ 2*q^(1/8:ℝ)≤q^(1/6:ℝ) ∧ |s.im|<q^(1/8:ℝ) ∧
        8≤m ∧ 20*q^(-(1/8:ℝ))<(m:ℝ)/t ∧ q^a≤(m:ℝ)/t) ∧
      (nominalQ eta t)^(7/8:ℝ)*(Real.log (nominalQ eta t))^5≤(nominalQ eta t)^(1-d) ∧
      (D/K)*(nominalQ eta t)^(1-d)<(nominalQ eta t)^(s.re+a*(5/2)) := by
    filter_upwards [hThresholds,hQ.eventually hError,
      hQ.eventually (eventually_strict_power_domination (D/K) hExp')] with t h₁ h₂ h₃
    exact ⟨h₁,h₂,h₃⟩
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hAll
  obtain ⟨t,ht,hexc⟩ := natural_mertens_excursions_of_zero hz hb.le hbβ hb1
    (max 1 (max J (max S T)))
  have ht0 : (0:ℝ)<t := by exact_mod_cast (show 0<t from (le_max_left 1 _).trans ht)
  have hbig := (le_max_right 1 _).trans ht
  have htJ := (le_max_left J _).trans hbig
  have htS := ((le_max_left S T).trans (le_max_right J _)).trans hbig
  have htT := ((le_max_right S T).trans (le_max_right J _)).trans hbig
  let q := nominalQ eta (t:ℝ)
  let m := crossingCount (2*t) t
  have hcnt : (m:ℝ)=|ArithmeticFourierInversion.M t| := crossingCount_abs (by omega : t≤2*t)
  have hMt : (t:ℝ)^b≤m := hcnt ▸ hexc
  obtain ⟨hAdm,hErr,hBad⟩ := hJ t htJ
  obtain ⟨hq,hFreeze,hHeight,hm,hLong,ha⟩ := hAdm m hMt
  have hq0 : 0<q := zero_lt_one.trans hq
  have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  obtain ⟨sample,hSample,hMove,hObs'⟩ := hObs t htS
  have hWin' := hWin t htT hq hFreeze hHeight hm hLong (B*q^(1-d))
    (by positivity) sample hSample hMove hObs'
  have hSum : C*(B*q^(1-d)+q^(7/8:ℝ)*(Real.log q)^5)≤D*q^(1-d) := by
    calc
      _ ≤ C*(B*q^(1-d)+q^(1-d)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hErr _) hC
      _ = _ := by dsimp [D]; ring
  have hCost : K*q^s.re*((m:ℝ)/t) ≤ D*q^(1-d)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m) :=
    hWin'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSum (by positivity)) (by positivity))
  have hUpper := ratio_cost_to_power hm0 ht0 hq0 hK hD hCost
  have hLower : q^(s.re+a*(5/2))≤q^s.re*((m:ℝ)/t)^(5/2:ℝ) := by
    rw [Real.rpow_add hq0,Real.rpow_mul hq0.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.rpow_nonneg hq0.le _) ha (by norm_num))
      (Real.rpow_nonneg hq0.le _)
  exact (not_lt_of_ge (hLower.trans hUpper)) hBad

theorem fixed_strip_iff_some_natural_long_row_power (hIngham : ZetaDensityPremise)
    {eta : ℝ} (he : 0<eta) (he1 : eta<1) :
    (∃ k : ℝ, 0<k ∧ ∀ s : ℂ, 1-k<s.re → riemannZeta s≠0) ↔
      (∃ d : ℝ, 0<d ∧ d≤1/8 ∧ UniformNaturalLongRowPower eta d) := by
  constructor
  · rintro ⟨k,hk,hStrip⟩
    let d := min k (1/8)
    refine ⟨d,lt_min hk (by norm_num),min_le_right _ _,real_power_implies_natural_power (right_strip_bounds_long_rows hIngham he ?_)⟩
    intro r
    by_contra! h
    have hz := hStrip (rightValue r) (by linarith [min_le_left k (1/8:ℝ)])
    exact hz r.val.property.2
  · rintro ⟨d,hd,hd1,hPower⟩
    refine ⟨d/(1+(5/2)*((1-eta)/eta)),by positivity,?_⟩
    intro s hs
    exact uniform_natural_long_row_power_forces_strip hIngham he he1 hd hd1 hPower hs

theorem natural_half_scale_eighth_saving_forces_27_28_strip (hIngham : ZetaDensityPremise)
    (hPower : UniformNaturalLongRowPower (1/2) (1/8))
    {s : ℂ} (hs : (27/28:ℝ)<s.re) : riemannZeta s≠0 := by
  apply uniform_natural_long_row_power_forces_strip hIngham
    (by norm_num : (0:ℝ)<1/2) (by norm_num) (by norm_num : (0:ℝ)<1/8) le_rfl hPower
  convert hs using 1
  norm_num

end RHConnections.LongRankPhase
