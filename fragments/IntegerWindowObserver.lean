import Verified
import IntegerPhaseSampling

noncomputable section
open Filter Set
namespace RHConnections.LongRankPhase
open RHConnections.RankContrast

def UniformNaturalLongRowPower (eta delta : ℝ) : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∀ᶠ n : ℕ in atTop, ∃ c : ℂ,
    let X := (n:ℝ)
    longRowCost X (X^eta) c ≤ C*Real.sqrt (⌊X/(X^eta)⌋₊:ℝ)*(X^eta)^(1-delta)

theorem real_power_implies_natural_power {eta delta : ℝ} (h : UniformLongRowPower eta delta) :
    UniformNaturalLongRowPower eta delta := by
  obtain ⟨C,hC,h⟩ := h
  exact ⟨C,hC,tendsto_natCast_atTop_atTop.eventually h⟩

theorem natural_power_observes_sample_windows {eta delta d W : ℝ}
    (he : 0<eta) (he1 : eta<1) (hSub : d≤delta) (hd : delta≤1)
    (hd0 : 0≤delta) (hW : W<Real.log (7/6))
    (hPower : UniformNaturalLongRowPower eta delta) :
    ∃ C : ℝ, 0≤C ∧ ∃ T : ℕ, ∀ t≥T,
      ∃ sample : ℝ → ℝ,
        (∀ z∈Icc 0 W, sample z∈Icc 0 (Real.log (7/6))) ∧
        (∀ z∈Icc 0 W, |scaleX eta t z-scaleX eta t (sample z)|≤1) ∧
        (∀ z∈Icc 0 W,∃ c : ℂ,
          longRowCost (scaleX eta t (sample z)) (scaleQ eta t (sample z)) c≤
            (C*(nominalQ eta t)^(1-d))*Real.sqrt (t:ℝ)) := by
  classical
  obtain ⟨C,hC,hEv⟩ := hPower
  obtain ⟨K,hK⟩ := eventually_atTop.mp hEv
  let margin := Real.log (7/6)-W
  have hMargin : 0<margin := sub_pos.mpr hW
  obtain ⟨T,hT⟩ := exists_nat_ge (max (max 4 (K:ℝ)) (1/margin))
  refine ⟨4*C,by positivity,T,?_⟩
  intro t ht
  have htR : (T:ℝ)≤t := by exact_mod_cast ht
  have ht4 : (4:ℝ)≤t := (le_max_left _ _).trans ((le_max_left _ _).trans (hT.trans htR))
  have ht4' : 4≤t := by exact_mod_cast ht4
  have htP : (0:ℝ)<t := by linarith
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
  let Q₀ := nominalQ eta (t:ℝ)
  have hLarge (z : ℝ) (hz : 0≤z) : (t:ℝ)≤scaleX eta (t:ℝ) z :=
    hNom.trans (le_mul_of_one_le_right (htP.le.trans hNom) (Real.one_le_exp_iff.mpr hz))
  have hSamples (z : ℝ) (hz : z∈Icc 0 W) :
      ∃ n : ℕ, ∃ zp∈Icc 0 (Real.log (7/6)), scaleX eta (t:ℝ) zp=(n:ℝ) ∧
        scaleX eta (t:ℝ) z≤(n:ℝ) ∧ (n:ℝ)<scaleX eta (t:ℝ) z+1 := by
    have hx := hLarge z hz.1
    have hx0 := htP.trans_le hx
    have h_inv : 1/scaleX eta (t:ℝ) z≤margin := by
      have hB := ((le_max_right (max 4 (K:ℝ)) (1/margin)).trans (hT.trans htR)).trans hx
      exact (div_le_iff₀ hx0).mpr (by
        have h := (div_le_iff₀ hMargin).mp hB
        nlinarith only [h])
    have hma : z+1/scaleX eta (t:ℝ) z≤Real.log (7/6) := by
      dsimp [margin] at h_inv
      linarith [hz.2]
    obtain ⟨n,zp,hzp,hX,hlo,hhi,_⟩ := actual_window_integer_sample htP he.le he1.le hz.1 hma
    exact ⟨n,zp,hzp,hX,hlo,hhi⟩
  choose n zp hzp hX hlo hhi using hSamples
  let sample (z : ℝ) := if hz : z∈Icc 0 W then zp z hz else 0
  have hsEq z (hz : z∈Icc 0 W) : sample z=zp z hz := dif_pos hz
  refine ⟨sample,?_,?_,?_⟩
  · intro z hz
    rw [hsEq z hz]
    exact hzp z hz
  · intro z hz
    rw [hsEq z hz,hX z hz,abs_of_nonpos (sub_nonpos.mpr (hlo z hz))]
    linarith [hhi z hz]
  intro z hz
  rw [hsEq z hz]
  let X := scaleX eta (t:ℝ) (zp z hz)
  let Q := scaleQ eta (t:ℝ) (zp z hz)
  let N := ⌊X/Q⌋₊
  have hz' := hzp z hz
  have hn : K≤n z hz := by
    exact_mod_cast (show (K:ℝ)≤(n z hz:ℝ) from
      ((le_max_right (4:ℝ) (K:ℝ)).trans ((le_max_left _ _).trans (hT.trans htR))).trans
        ((hLarge z hz.1).trans (hlo z hz)))
  obtain ⟨c,hc⟩ := hK (n z hz) hn
  have hXPos : 0<X := htP.trans_le (hLarge (zp z hz) hz'.1)
  have hQ1 : 1≤Q₀ := Real.one_le_rpow (by linarith) he.le
  have hQpos : 0<Q := (zero_lt_one.trans_le hQ1).trans_le
    (scaleQ_window he he1 htP hz'.1 hz'.2).1
  have hQle : Q≤2*Q₀ := (scaleQ_window he he1 htP hz'.1 hz'.2).2.trans (by linarith)
  have hNle : (N:ℝ)≤2*(t:ℝ) := by
    have hRatio := (scaleN_window he he1 ht4' hz'.1 hz'.2).2.2
    exact (Nat.floor_le (div_nonneg (hXPos.le) hQpos.le)).trans
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
  have hXeq : (n z hz:ℝ)=X := (hX z hz).symm
  dsimp only at hc
  rw [hXeq] at hc
  change longRowCost X Q c≤C*Real.sqrt (N:ℝ)*Q^(1-delta) at hc
  refine ⟨c,hc.trans ?_⟩
  change C*Real.sqrt (N:ℝ)*Q^(1-delta)≤4*C*Q₀^(1-d)*Real.sqrt (t:ℝ)
  calc
    _ = C*(Real.sqrt (N:ℝ)*Q^(1-delta)) := by ring
    _ ≤ C*((2*Real.sqrt (t:ℝ))*(2*Q₀^(1-d))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hSqrt hPow (by positivity) (by positivity)) hC
    _ = _ := by ring

end RHConnections.LongRankPhase
