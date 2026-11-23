import Verified
import FrozenPotentialShift
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

theorem actual_sampled_rank_window_inequality (hIngham : ZetaDensityPremise)
    {eta W : ℝ} (he : 0<eta) (he1 : eta<1) (target : RightZero)
    (hW : 0<W) (hW' : W≤Real.log (7/6)) :
    ∃ C : ℝ, 0≤C ∧ ∃ T : ℕ, ∀ t≥T,
      let Q₀ := nominalQ eta (t:ℝ)
      let m := crossingCount (2*t) t
      1<Q₀ → 2*Q₀^(1/8:ℝ)≤Q₀^(1/6:ℝ) → |(rightValue target).im|<Q₀^(1/8:ℝ) →
      8≤m → 20*Q₀^(-(1/8:ℝ)) < (m:ℝ)/t →
      ∀ U : ℝ, 0≤U → ∀ sample : ℝ → ℝ,
        (∀ z∈Icc 0 W, sample z ∈ Icc 0 (Real.log (7/6))) →
        (∀ z∈Icc 0 W, |scaleX eta t z-scaleX eta t (sample z)|≤1) →
        (∀ z∈Icc 0 W,∃ c : ℂ,
          longRowCost (scaleX eta t (sample z)) (scaleQ eta t (sample z)) c≤U*Real.sqrt (t:ℝ)) →
        (‖rightValue target-1‖/8)*Q₀^(rightValue target).re*((m:ℝ)/t) ≤
          C*(U+Q₀^(7/8:ℝ)*(Real.log Q₀)^5)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m) := by
  let rho₀ := rightValue target
  have hρpos : 0<rho₀.re := target.val.property.1.1
  have hρ1 : rho₀.re<1 := target.val.property.1.2
  have hρ0 : rho₀≠0 := by intro h; rw [h,Complex.zero_re] at hρpos; exact (lt_irrefl _ hρpos)
  have hρne : rho₀≠1 := by intro h; rw [h,Complex.one_re] at hρ1; exact (lt_irrefl _ hρ1)
  let rho := otherRightValue target
  obtain ⟨C₁,hC₁,hcount⟩ := shifted_other_count hIngham target
  obtain ⟨R,D,hR,hD,hphase⟩ := frozen_rank_window_obstruction (ι := ℕ) rho₀ hρ0 hρne rho
    (fun r hr => r.property (right_value_injective hr)) (shifted_other_near_finite target)
    hC₁ hW hcount
  obtain ⟨T,hgeo⟩ := actual_normalized_window he he1 hR
  obtain ⟨C,hC,hfreeze⟩ := freeze_spectral_rows_from_density hIngham
  obtain ⟨F,hF,hLip⟩ := right_potential_frozen_lipschitz hIngham
  let errorCoeff := 80*C+2*F*(1+R)
  have hCoeff : 0≤errorCoeff := by dsimp [errorCoeff]; positivity
  let totalCoeff := 4*(errorCoeff+16*C)
  have hTotal : 0≤totalCoeff := by dsimp [totalCoeff]; positivity
  refine ⟨D*(24+totalCoeff),by positivity,max 4 T,?_⟩
  intro t ht
  dsimp only
  intro hQ₀ hThreshold hTarget hm hLong U hU sample hSample hMove hObs
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
  let rawX (z : ℝ) := scaleX eta (t:ℝ) z
  let X (z : ℝ) := rawX (sample z)
  let Q (z : ℝ) := scaleQ eta (t:ℝ) (sample z)
  let grid (z : ℝ) (i : ℕ) := ((rowStartLength (X z) (Q z) (.pair,i)).2:ℝ)
  let value (z : ℝ) (i : ℕ) := longRowValue (X z) (Q z) (.pair,i)
  let scale (z : ℝ) := (X z/(t:ℝ))/realDyadicMeshWidth (Q z)
  have hqBounds (z : ℝ) (hz : z∈Icc 0 W) : Q₀≤Q z ∧ Q z≤2*Q₀ := by
    have hg := scaleQ_window he he1 htP (hSample z hz).1 (hSample z hz).2
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
        (fun i hi => by simpa [signSet] using (hGeometry.2.2.2 (sample z) (hSample z hz) i hi).2.2.1)
      exact h.trans ((mul_le_mul_of_nonneg_left (hc2.trans hc) (by positivity)).trans_eq (by ring))
  have hWindow (z : ℝ) (hz : z∈Icc 0 W) (i : ℕ) (hi : i∈I) :
      |grid z i-scale z*(b i-a i)|≤4 ∧
      ‖(rightPotential Q₀ ((X z/t)*b i)-rightPotential Q₀ ((X z/t)*a i))-value z i‖≤80*C*E := by
    obtain ⟨hA',hB',hi',hstab⟩ := hGeometry.2.2.2 (sample z) (hSample z hz) i hi
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
    have hScale := (scaleN_window he he1 ht4 (hSample z hz).1 (hSample z hz).2).2.1
    have hX : 0<X z := by dsimp [X,rawX,scaleX]; positivity
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
  have hEndpointMove (z : ℝ) (hz : z∈Icc 0 W) {y : ℝ} (hy₀ : 0≤y)
      (hy₁ : y≤1+R) : |(rawX z/t)*y-(X z/t)*y|≤1+R := by
    have ht1 : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
    have h := hMove z hz
    change |rawX z-X z|≤1 at h
    have hg : |(rawX z/t)*y-(X z/t)*y|=|rawX z-X z| * y/t := by
      rw [show rawX z / (t:ℝ)*y-X z/(t:ℝ)*y=(rawX z-X z)*y/(t:ℝ) by ring,
        abs_div,abs_mul,abs_of_nonneg hy₀,abs_of_pos htP]
    rw [hg]
    apply (div_le_iff₀ htP).mpr
    calc
      _ ≤ 1*y := mul_le_mul_of_nonneg_right h hy₀
      _ ≤ (1+R)*1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left ht1 (by positivity)
  have hFrozen (z : ℝ) (hz : z∈Icc 0 W) (i : ℕ) (hi : i∈I) :
      ‖(rightPotential Q₀ ((rawX z/t)*b i)-rightPotential Q₀ ((rawX z/t)*a i))-value z i‖≤errorCoeff*E := by
    have hrawBounds := hGeometry.2.2.2 z ⟨hz.1,hz.2.trans hW'⟩ i hi
    have hrawQ := (scaleQ_window he he1 htP hz.1 (hz.2.trans hW')).1
    have hsampleBounds := hGeometry.2.2.2 (sample z) (hSample z hz) i hi
    have hsQ := (hqBounds z hz).1
    have hRng := hGeometry.2.1 i hi
    have hB₀ : 0≤b i := by linarith [hRng.1,hRng.2.1,hlen]
    have hShift := frozen_interval_change_bound (rightPotential Q₀)
      (show 0≤F*(Real.log Q₀)^5 by positivity [Real.log_nonneg hQ₀.le])
      (hLip Q₀ hQ₀ hThreshold)
      (hrawQ.trans hrawBounds.1.1) (hrawQ.trans hrawBounds.2.1.1)
      (hsQ.trans hsampleBounds.1.1) (hsQ.trans hsampleBounds.2.1.1)
      (hEndpointMove z hz hRng.1.le hRng.2.2.1.2.le)
      (hEndpointMove z hz hB₀ hRng.2.2.2.2.le)
    have hscale : F*(Real.log Q₀)^5*((1+R)+(1+R))≤(2*F*(1+R))*E := by
      have h := Real.one_le_rpow hQ₀.le (by norm_num : (0:ℝ)≤7/8)
      calc
        _ = (2*F*(1+R)*(Real.log Q₀)^5)*1 := by ring
        _ ≤ (2*F*(1+R)*(Real.log Q₀)^5)*Q₀^(7/8:ℝ) :=
          mul_le_mul_of_nonneg_left h (by positivity [Real.log_nonneg hQ₀.le])
        _ = _ := by dsimp [E]; ring
    have hFroz := (hWindow z hz i hi).2
    let f (w : ℝ) := rightPotential Q₀ (w/t*b i)-rightPotential Q₀ (w/t*a i)
    change ‖f (rawX z)-f (X z)‖≤_ at hShift
    change ‖f (X z)-value z i‖≤_ at hFroz
    change ‖f (rawX z)-value z i‖≤_
    have htri : ‖f (rawX z)-value z i‖≤‖f (rawX z)-f (X z)‖+‖f (X z)-value z i‖ := by
      simpa only [dist_eq_norm] using dist_triangle (f (rawX z)) (f (X z)) (value z i)
    exact htri.trans
      ((add_le_add (hShift.trans hscale) hFroz).trans_eq (by dsimp [errorCoeff]; ring))
  have hWeight (r : OtherRightZero target) : rho r≠0 := by
    intro h
    have hp : 0<(rho r).re := r.val.val.property.1.1
    simp [h] at hp
  have hRaw := hphase hA hB (Finset.subset_union_left) (Finset.subset_union_right)
    a b ((m:ℝ)/(4*t)) L₀ (zeroMultiplicity target) hgap hL₀
    (by unfold zeroMultiplicity; positivity) roots mult (fun r _ => hWeight r)
    ((m:ℝ)/(2*t)) (errorCoeff*E) 4 (4*C*E) (Real.sqrt 2*U*Real.sqrt (t:ℝ))
    hlen (by positivity) (by norm_num) (by positivity) grid value scale
    (fun i hi => hGeometry.2.1 i (Finset.mem_union.mpr hi)) hGeometry.2.2.1 hcost
    (fun z hz i hi => (hWindow z hz i (Finset.mem_union.mpr hi)).1) (by
      intro z hz
      dsimp only
      intro i hi
      have heq : L₀*Real.exp z = rawX z/(t:ℝ) := by dsimp [L₀,rawX,scaleX]; ring
      rw [heq]
      have hpoint (x : ℝ) : rightPotential Q₀ x=(zeroMultiplicity target:ℂ)*zeroPrimitive rho₀ x+
          ∑ j∈roots,mult j*zeroPrimitive (rho j) x := right_potential_target_split target Q₀ hTarget x
      have he : (zeroMultiplicity target:ℂ)*
            (zeroPrimitive rho₀ (rawX z/t*b i)-zeroPrimitive rho₀ (rawX z/t*a i))+
          (∑ j∈roots,mult j*(zeroPrimitive (rho j) (rawX z/t*b i)-zeroPrimitive (rho j) (rawX z/t*a i))) =
            rightPotential Q₀ (rawX z/t*b i)-rightPotential Q₀ (rawX z/t*a i) := by
        rw [hpoint,hpoint]
        simp only [mul_sub,Finset.sum_sub_distrib]
        ring
      rw [he]
      exact (hFrozen z hz i (Finset.mem_union.mpr hi)))
  have hAlg := quarter_row_cost_algebra (t := (t:ℝ)) (m := (m:ℝ))
    hmP htM hGeometry.1.1 hGeometry.1.2
    (U := Real.sqrt 2*U) (E := errorCoeff*E+4*C*E*4) (by positivity) (by positivity)
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
  rw [show D*(24+totalCoeff)*(U+E)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m) =
      D*((24+totalCoeff)*(U+E)*((t:ℝ)/m)*Real.sqrt ((t:ℝ)/m)) by ring]
  apply mul_le_mul_of_nonneg_left _ hD
  refine hAlg.trans ?_
  have hUE : 12*(Real.sqrt 2*U)+4*(errorCoeff*E+4*C*E*4)≤(24+totalCoeff)*(U+E) := by
    have heq : 4*(errorCoeff*E+4*C*E*4)=totalCoeff*E := by dsimp [totalCoeff]; ring
    rw [heq]
    nlinarith only [mul_le_mul_of_nonneg_right h2 hU,mul_nonneg hTotal hU,
      mul_nonneg hE (by norm_num : (0:ℝ)≤24)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUE (by positivity)) (by positivity))

end RHConnections.LongRankPhase
