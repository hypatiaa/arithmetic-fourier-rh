import Verified
import ActualNormalizedRankWindow
import ActualTargetZeroSet
import LongRankGridConnection
import FreezeActualSpectralRows
import ObservableLongRows
import ActualLongRankCenter
import WindowCostAlgebra

noncomputable section
open Set Filter
namespace RHConnections.LongRankPhase
open RHConnections.RankPairing RHConnections.BlockFourier RHConnections.PhaseWindow
open RHConnections.RankContrast RHConnections.MobiusCrossingLengths RHConnections.MobiusRankLocalization
open RHConnections.LocalModeContrast

theorem actual_frozen_rank_window_inequality (hIngham : ZetaDensityPremise)
    {eta : ℝ} (he : 0<eta) (he1 : eta<1) (target : RightZero) :
    ∃ C : ℝ, 0≤C ∧ ∃ T : ℕ, ∀ t≥T,
      let Q₀ := nominalQ eta (t:ℝ)
      let m := crossingCount (2*t) t
      1<Q₀ → 2*Q₀^(1/8:ℝ)≤Q₀^(1/6:ℝ) → |(rightValue target).im|<Q₀^(1/8:ℝ) →
      8≤m → 20*Q₀^(-(1/8:ℝ)) < (m:ℝ)/t →
      ∀ U : ℝ, 0≤U →
        (∀ z∈Icc 0 (Real.log (7/6)),∃ c : ℂ,
          longRowCost (scaleX eta t z) (scaleQ eta t z) c≤U*Real.sqrt (t:ℝ)) →
        (‖rightValue target-1‖/8)*Q₀^(rightValue target).re*((m:ℝ)/t) ≤
          C*(U+Q₀^(7/8:ℝ)*(Real.log Q₀)^5)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m) := by
  let rho₀ := rightValue target
  have hρpos : 0<rho₀.re := target.val.property.1.1
  have hρ1 : rho₀.re<1 := target.val.property.1.2
  have hρ0 : rho₀≠0 := by intro h; rw [h,Complex.zero_re] at hρpos; exact (lt_irrefl _ hρpos)
  have hρne : rho₀≠1 := by intro h; rw [h,Complex.one_re] at hρ1; exact (lt_irrefl _ hρ1)
  let rho := otherRightValue target
  let W := Real.log (7/6)
  have hW : 0<W := Real.log_pos (by norm_num)
  obtain ⟨C₁,hC₁,hcount⟩ := shifted_other_count hIngham target
  obtain ⟨R,D,hR,hD,hphase⟩ := frozen_rank_window_obstruction (ι := ℕ) rho₀ hρ0 hρne rho
    (fun r hr => r.property (right_value_injective hr)) (shifted_other_near_finite target)
    hC₁ hW hcount
  obtain ⟨T,hgeo⟩ := actual_normalized_window he he1 hR
  obtain ⟨C,hC,hfreeze⟩ := freeze_spectral_rows_from_density hIngham
  refine ⟨D*(24+384*C),by positivity,max 4 T,?_⟩
  intro t ht
  dsimp only
  intro hQ₀ hThreshold hTarget hm hLong U hU hObs
  have ht4 : 4≤t := (le_max_left _ _).trans ht
  have htP : (0:ℝ)<t := by exact_mod_cast (by omega : 0<t)
  let Q₀ := nominalQ eta (t:ℝ)
  let L₀ := nominalX eta (t:ℝ)/(t:ℝ)
  let m := crossingCount (2*t) t
  let A := firstQuarterRanks (lowerRank t) m
  let B := lastQuarterRanks (lowerRank t) m
  let I := A∪B
  let a := normalizedA t
  let b := normalizedB t
  let E := Q₀^(7/8:ℝ)*(Real.log Q₀)^5
  let roots := otherHeightFinset target (Q₀^(1/8:ℝ))
  let mult (r : OtherRightZero target) : ℂ := (zeroMultiplicity r.val:ℂ)
  have hL₀ : 0<L₀ := by dsimp [L₀,nominalX]; positivity
  have hmP : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hm8 : (0:ℝ)<(m:ℝ)/8 := by positivity
  have hE : 0≤E := by dsimp [E]; positivity [Real.log_nonneg hQ₀.le]
  have hQ₀p : 0<Q₀ := zero_lt_one.trans hQ₀
  have hGeometry := hgeo t ((le_max_right 4 T).trans ht) hm
  have hA : A.Nonempty := Finset.card_pos.mp
    (by exact_mod_cast hm8.trans_le hGeometry.1.1)
  have hB : B.Nonempty := Finset.card_pos.mp
    (by exact_mod_cast hm8.trans_le hGeometry.1.2)
  have hlen : (0:ℝ)<(m:ℝ)/(2*t) := by positivity
  have hgap : (0:ℝ)<(m:ℝ)/(4*t) := by positivity
  have hU' : 0≤Real.sqrt 2*U*Real.sqrt (t:ℝ) := by positivity
  have hXNom : 0<nominalX eta (t:ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hQ₀L : L₀=(3/2)*Q₀ := by
    have h := scaled_ratio_identity he1 htP 0
    have hh : nominalX eta (t:ℝ)/Q₀=3*(t:ℝ)/2 := by
      simpa [scaleX,scaleQ,Q₀,nominalQ] using h
    have h' := (div_eq_iff hQ₀p.ne').mp hh
    change nominalX eta (t:ℝ)/(t:ℝ)=_
    apply (div_eq_iff htP.ne').mpr
    linear_combination h'
  have htM : (m:ℝ)≤t := by
    have hN : t≤2*t := by omega
    have hM : (m:ℝ)=|ArithmeticFourierInversion.M t| := crossingCount_abs hN
    calc
      _ = _ := hM
      _ ≤ (t:ℝ) := by
        unfold ArithmeticFourierInversion.M
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc
          _ ≤ ∑ _i∈Finset.Ioc 0 t,(1:ℝ) :=
            Finset.sum_le_sum (fun i _ => by
              change |(ArithmeticFunction.moebius i:ℝ)| ≤ 1
              exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i)))
          _ = _ := by simp [Nat.card_Ioc]
  let X (z : ℝ) := scaleX eta (t:ℝ) z
  let Q (z : ℝ) := scaleQ eta (t:ℝ) z
  let grid (z : ℝ) (i : ℕ) := ((rowStartLength (X z) (Q z) (.pair,i)).2:ℝ)
  let value (z : ℝ) (i : ℕ) := longRowValue (X z) (Q z) (.pair,i)
  let scale (z : ℝ) := (X z/(t:ℝ))/realDyadicMeshWidth (Q z)
  have hqBounds (z : ℝ) (hz : z∈Icc 0 W) : Q₀≤Q z ∧ Q z≤2*Q₀ := by
    have hg := scaleQ_window he he1 htP hz.1 hz.2
    exact ⟨hg.1,hg.2.trans (by change (7/6)*Q₀≤2*Q₀; linarith)⟩
  have hH (z : ℝ) (hz : z∈Icc 0 W) : realDyadicMeshWidth (Q z) ≤ 2*Q₀^(7/8:ℝ) := by
    unfold realDyadicMeshWidth
    have hh := Real.sqrt_le_sqrt (hqBounds z hz).2
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at hh
    have h2 : Real.sqrt 2≤2 :=
      (Real.sqrt_le_sqrt (by norm_num : (2:ℝ)≤2^2)).trans_eq (Real.sqrt_sq (by norm_num))
    have h3 : Real.sqrt Q₀≤Q₀^(7/8:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hQ₀.le (by norm_num)
    exact hh.trans (mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by norm_num))
  have hcost z (hz : z∈Icc 0 W) :
      ∃ c : ℂ, ‖c‖≤4*C*E ∧
        Real.sqrt (∑ i∈I,‖value z i-c*(grid z i:ℂ)‖^2)≤
          Real.sqrt 2*U*Real.sqrt (t:ℝ) := by
    obtain ⟨c,hc⟩ := hObs z hz
    have hf := hfreeze Q₀ (Q z) hQ₀ hThreshold (hqBounds z hz).1 (hqBounds z hz).2
    obtain ⟨c',hc1,hc2⟩ := improve_long_row_center (X z) (Q z)
      (hQ₀.le.trans (hqBounds z hz).1)
      (show 0≤C*(Real.log Q₀)^5 by positivity [Real.log_nonneg hQ₀.le]) hf.1 c
    refine ⟨c',hc1.trans ?_,?_⟩
    · have h := mul_le_mul_of_nonneg_left (hH z hz)
        (show 0≤C*(Real.log Q₀)^5 by positivity [Real.log_nonneg hQ₀.le])
      dsimp [E]
      nlinarith only [h]
    · have h := paired_subfamily_cost_bound (X z) (Q z) c' I
        (fun i hi => by simpa [signSet] using (hGeometry.2.2.2 z hz i hi).2.2.1)
      exact h.trans ((mul_le_mul_of_nonneg_left (hc2.trans hc) (by positivity)).trans_eq (by ring))
  have hWindow (z : ℝ) (hz : z∈Icc 0 W) (i : ℕ) (hi : i∈I) :
      |grid z i-scale z*(b i-a i)|≤4 ∧
      ‖(rightPotential Q₀ ((X z/t)*b i)-rightPotential Q₀ ((X z/t)*a i))-value z i‖≤80*C*E := by
    obtain ⟨hA',hB',hi',hstab⟩ := hGeometry.2.2.2 z hz i hi
    have hab : a i≤b i := by linarith only [(hGeometry.2.1 i hi).2.1,hlen]
    have hEp : (rowEndpoints ⌊X z/Q z⌋₊ (.pair,i))=(lowerEndpoint t i,upperEndpoint t i) := by
      unfold rowEndpoints lowerEndpoint upperEndpoint
      change (min (indexAt (signSet true _) i) (indexAt (signSet false _) i),
        max (indexAt (signSet true _) i) (indexAt (signSet false _) i))=_
      rw [hstab true,hstab false]
    have hEa : X z/(upperEndpoint t i:ℝ)=(X z/t)*a i := by
      dsimp [a,normalizedA]
      rw [←mul_div_assoc,div_mul_cancel₀ _ htP.ne']
    have hEb : X z/(lowerEndpoint t i:ℝ)=(X z/t)*b i := by
      dsimp [b,normalizedB]
      rw [←mul_div_assoc,div_mul_cancel₀ _ htP.ne']
    have hScale := (scaleN_window he he1 ht4 hz.1 hz.2).2.1
    have hX : 0<X z := by dsimp [X,scaleX]; positivity
    have hMul : (3/2)*(Q z)≤X z/(t:ℝ) := by
      have hqp : 0<Q z := hQ₀p.trans_le (hqBounds z hz).1
      have h := (le_div_iff₀ hqp).mp hScale
      apply (le_div_iff₀ htP).mpr
      linarith only [h]
    have hShort : 12*Q z*Q₀^(-(1/8:ℝ)) < (X z/t)*b i-(X z/t)*a i := by
      rw [←mul_sub]
      have h₁ := mul_le_mul hMul (hGeometry.2.1 i hi).2.1 hlen.le (by positivity)
      have h₂ := mul_lt_mul_of_pos_left hLong (show 0<Q z by exact hQ₀p.trans_le (hqBounds z hz).1)
      have hE : (m:ℝ)/(2*t)=((m:ℝ)/t)/2 := by ring
      rw [hE] at h₁
      nlinarith only [h₁,h₂,mul_pos (show 0<Q z by exact hQ₀p.trans_le (hqBounds z hz).1)
        (Real.rpow_pos_of_pos hQ₀p (-(1/8:ℝ)))]
    have hGrid := row_grid_connection (X z) (Q z) Q₀ ((X z/t)*a i) ((X z/t)*b i)
      (.pair,i) hQ₀.le (hqBounds z hz).1 hA' hB'
      (mul_le_mul_of_nonneg_left hab (by positivity))
      (by rw [hEp,hEa]) (by rw [hEp,hEb]) hShort
    have hSt := (hfreeze Q₀ (Q z) hQ₀ hThreshold (hqBounds z hz).1 (hqBounds z hz).2).2
      ((X z/t)*a i) hA' ((X z/t)*b i) hB' (mul_le_mul_of_nonneg_left hab (by positivity))
    constructor
    · have heq : (X z/t*b i-X z/t*a i)/realDyadicMeshWidth (Q z) =
          scale z*(b i-a i) := by dsimp [scale]; ring
      rw [heq] at hGrid
      exact hGrid.1
    · rw [norm_sub_rev, show value z i=shellSpectrumRow (Q z) ((X z/t)*a i) ((X z/t)*b i) from hGrid.2]
      exact hSt.trans_eq (by dsimp [E]; ring)
  have hWeight (r : OtherRightZero target) : rho r≠0 := by
    intro h
    have hp : 0<(rho r).re := r.val.val.property.1.1
    simp [h] at hp
  have hRaw := hphase hA hB (Finset.subset_union_left) (Finset.subset_union_right)
    a b ((m:ℝ)/(4*t)) L₀ (zeroMultiplicity target) hgap hL₀
    (by unfold zeroMultiplicity; positivity) roots mult (fun r _ => hWeight r)
    ((m:ℝ)/(2*t)) (80*C*E) 4 (4*C*E) (Real.sqrt 2*U*Real.sqrt (t:ℝ))
    hlen (by positivity) (by norm_num) (by positivity) grid value scale
    (fun i hi => hGeometry.2.1 i (Finset.mem_union.mpr hi)) hGeometry.2.2.1 hcost
    (fun z hz i hi => (hWindow z hz i (Finset.mem_union.mpr hi)).1) (by
      intro z hz
      dsimp only
      intro i hi
      have heq : L₀*Real.exp z = X z/(t:ℝ) := by dsimp [L₀,X,scaleX]; ring
      rw [heq]
      have hpoint (x : ℝ) : rightPotential Q₀ x=(zeroMultiplicity target:ℂ)*zeroPrimitive rho₀ x+
          ∑ j∈roots,mult j*zeroPrimitive (rho j) x := right_potential_target_split target Q₀ hTarget x
      have he : (zeroMultiplicity target:ℂ)*
            (zeroPrimitive rho₀ (X z/t*b i)-zeroPrimitive rho₀ (X z/t*a i))+
          (∑ j∈roots,mult j*(zeroPrimitive (rho j) (X z/t*b i)-zeroPrimitive (rho j) (X z/t*a i))) =
            rightPotential Q₀ (X z/t*b i)-rightPotential Q₀ (X z/t*a i) := by
        rw [hpoint,hpoint]
        simp only [mul_sub,Finset.sum_sub_distrib]
        ring
      rw [he]
      exact (hWindow z hz i (Finset.mem_union.mpr hi)).2)
  have hAlg := quarter_row_cost_algebra (t := (t:ℝ)) (m := (m:ℝ))
    hmP htM hGeometry.1.1 hGeometry.1.2
    (U := Real.sqrt 2*U) (E := 80*C*E+4*C*E*4) (by positivity) (by positivity)
  have h2 : Real.sqrt 2≤2 :=
    (Real.sqrt_le_sqrt (by norm_num : (2:ℝ)≤2^2)).trans_eq (Real.sqrt_sq (by norm_num))
  have hM₀ : 1≤zeroMultiplicity target := by
    unfold zeroMultiplicity
    obtain ⟨ha,hord⟩ := SpectralTail.zeta_nontrivial_zero_finite_order target.val
    exact_mod_cast (Nat.succ_le_of_lt (SpectralTail.zero_order_positive target.val.property.2 ha hord))
  have hLpow : Q₀^rho₀.re≤L₀^rho₀.re := Real.rpow_le_rpow hQ₀p.le (by rw [hQ₀L]; linarith) hρpos.le
  have hLeft : (‖rho₀-1‖/8)*Q₀^rho₀.re*((m:ℝ)/t) ≤
      zeroMultiplicity target*L₀^rho₀.re*((m:ℝ)/(4*t))*‖rho₀-1‖/2 := by
    have h := hLpow.trans (le_mul_of_one_le_left (by positivity) hM₀)
    have hh := mul_le_mul_of_nonneg_right h
      (show 0≤(‖rho₀-1‖/8)*((m:ℝ)/t) by positivity)
    convert hh using 1 <;> ring
  refine (hLeft.trans hRaw).trans ?_
  rw [show D*(24+384*C)*(U+E)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m) =
      D*((24+384*C)*(U+E)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m)) by ring]
  apply mul_le_mul_of_nonneg_left _ hD
  refine hAlg.trans ?_
  have hUE : 12*(Real.sqrt 2*U)+4*(80*C*E+4*C*E*4)≤(24+384*C)*(U+E) := by
    nlinarith only [mul_le_mul_of_nonneg_right h2 hU,mul_nonneg hC hU,mul_nonneg hE (by norm_num : (0:ℝ)≤24)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUE (by positivity)) (by positivity))

end RHConnections.LongRankPhase
