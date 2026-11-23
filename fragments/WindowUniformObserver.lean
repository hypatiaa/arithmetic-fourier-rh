import Verified

noncomputable section
open Filter Set
namespace RHConnections.LongRankPhase
open RHConnections.RankContrast

theorem uniform_power_observes_scale_windows {eta delta d : ℝ}
    (he : 0<eta) (he1 : eta<1) (hSub : d≤delta) (hd : delta≤1)
    (hd0 : 0≤delta) (hPower : UniformLongRowPower eta delta) :
    ∃ C : ℝ, 0≤C ∧ ∃ T : ℕ, ∀ t≥T,
      ∀ z∈Icc 0 (Real.log (7/6)), ∃ c : ℂ,
        longRowCost (scaleX eta t z) (scaleQ eta t z) c≤
          (C*(nominalQ eta t)^(1-d))*Real.sqrt (t:ℝ) := by
  obtain ⟨C,hC,hEv⟩ := hPower
  obtain ⟨K,hK⟩ := eventually_atTop.mp hEv
  obtain ⟨T,hT⟩ := exists_nat_ge (max 4 K)
  refine ⟨4*C,by positivity,T,?_⟩
  intro t ht z hz
  have htR : (T:ℝ)≤t := by exact_mod_cast ht
  have ht4 : (4:ℝ)≤t := (le_max_left _ _).trans (hT.trans htR)
  have ht4' : 4≤t := by exact_mod_cast ht4
  have htP : (0:ℝ)<t := by linarith
  let X := scaleX eta (t:ℝ) z
  let Q := scaleQ eta (t:ℝ) z
  let Q₀ := nominalQ eta (t:ℝ)
  let N := ⌊X/Q⌋₊
  have hb : 1≤3*(t:ℝ)/2 := by linarith
  have hInv : 1≤(1-eta)⁻¹ := by
    rw [←one_div]
    exact (le_div_iff₀ (sub_pos.mpr he1)).mpr (by linarith)
  have hNom : (t:ℝ)≤nominalX eta (t:ℝ) := by
    calc
      (t:ℝ) ≤ 3*(t:ℝ)/2 := by linarith
      _ ≤ _ := by
        unfold nominalX
        simpa using Real.rpow_le_rpow_of_exponent_le hb hInv
  have hXNom : nominalX eta (t:ℝ)≤X := by
    exact le_mul_of_one_le_right (htP.le.trans hNom) (Real.one_le_exp_iff.mpr hz.1)
  have hX : K≤X := (le_max_right _ _).trans (hT.trans (htR.trans (hNom.trans hXNom)))
  obtain ⟨c,hc⟩ := hK X hX
  have hQ1 : 1≤Q₀ := Real.one_le_rpow (by linarith) he.le
  have hQpos : 0<Q := (zero_lt_one.trans_le hQ1).trans_le
    (scaleQ_window he he1 htP hz.1 hz.2).1
  have hQle : Q≤2*Q₀ := (scaleQ_window he he1 htP hz.1 hz.2).2.trans (by linarith)
  have hNle : (N:ℝ)≤2*(t:ℝ) := by
    have hRatio := (scaleN_window he he1 ht4' hz.1 hz.2).2.2
    exact (Nat.floor_le (div_nonneg (htP.le.trans (hNom.trans hXNom)) hQpos.le)).trans
      (hRatio.trans (by linarith))
  have hSqrt : Real.sqrt (N:ℝ)≤2*Real.sqrt (t:ℝ) := by
    have hh := Real.sqrt_le_sqrt hNle
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at hh
    have h2 : Real.sqrt 2≤2 := by
      exact (Real.sqrt_le_sqrt (by norm_num : (2:ℝ)≤2^2)).trans_eq
        (Real.sqrt_sq (by norm_num))
    exact hh.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))
  have hPow : Q^(1-delta)≤2*Q₀^(1-d) := by
    refine (Real.rpow_le_rpow hQpos.le hQle (sub_nonneg.mpr hd)).trans ?_
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (zero_le_one.trans hQ1)]
    have h2 : (2:ℝ)^(1-delta)≤2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (show 1-delta≤1 by linarith)
    exact mul_le_mul h2 (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
      (Real.rpow_nonneg (zero_le_one.trans hQ1) _) (by norm_num)
  change longRowCost X Q c≤C*Real.sqrt (N:ℝ)*Q^(1-delta) at hc
  refine ⟨c,hc.trans ?_⟩
  change C*Real.sqrt (N:ℝ)*Q^(1-delta)≤4*C*Q₀^(1-d)*Real.sqrt (t:ℝ)
  calc
    _ = C*(Real.sqrt (N:ℝ)*Q^(1-delta)) := by ring
    _ ≤ C*((2*Real.sqrt (t:ℝ))*(2*Q₀^(1-d))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hSqrt hPow (by positivity) (by positivity)) hC
    _ = _ := by ring

end RHConnections.LongRankPhase
