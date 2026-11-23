import Verified

noncomputable section
open Set
namespace RHConnections.LongRankPhase
open RHConnections.RankPairing RHConnections.BlockFourier RHConnections.PhaseWindow
open RHConnections.LocalModeContrast

def shellSpectrumRow (Q a b : ℝ) : ℂ :=
  let J := realDyadicMeshCount Q
  let R := realDyadicMeshRadius Q
  let u := realDyadicMeshPoint Q
  let ka := realActiveLength J u a
  let kb := realActiveLength J u b
  if hj : 0<J then
    letI : NeZero J := ⟨hj.ne'⟩
    complexIntervalSum (smoothComplexPositive (smoothingKernel R) (shellBlockSignal u (rightPotential Q)))
      (ka:ZMod J) (kb-ka)
  else 0

theorem right_height_mono : Monotone rightHeightFinset := by
  intro T U h r hr
  apply (right_height_finite U).mem_toFinset.mpr
  have hh : |(rightValue r).im|<T := (right_height_finite T).mem_toFinset.mp hr
  exact hh.trans_le h

theorem freeze_spectral_rows_from_density (hIngham : ZetaDensityPremise) :
    ∃ C : ℝ, 0≤C ∧ ∀ Q₀ Q : ℝ, 1<Q₀ → 2*Q₀^(1/8:ℝ)≤Q₀^(1/6:ℝ) →
      Q₀≤Q → Q≤2*Q₀ →
      (∀ a∈Icc Q (2*Q),∀ b∈Icc Q (2*Q),
        ‖rightPotential Q b-rightPotential Q a‖≤C*(Real.log Q₀)^5*|b-a|) ∧
      (∀ a∈Icc Q (2*Q),∀ b∈Icc Q (2*Q),a≤b →
        ‖shellSpectrumRow Q a b-(rightPotential Q₀ b-rightPotential Q₀ a)‖≤
          80*C*Q₀^(7/8:ℝ)*(Real.log Q₀)^5) := by
  classical
  obtain ⟨C,hC,hCount⟩ := weighted_right_finset hIngham
  refine ⟨C,hC,?_⟩
  intro Q₀ Q hQ₀ hTbound hQ₀Q hQupper
  have hQ : 1≤Q := hQ₀.le.trans hQ₀Q
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hQ₀p : 0<Q₀ := zero_lt_one.trans hQ₀
  let T := 2*Q₀^(1/8:ℝ)
  let logCost := C*(Real.log Q₀)^5
  let B := 4*Q*logCost/Q₀^(1/8:ℝ)
  let small := rightHeightFinset (Q₀^(1/8:ℝ))
  let big := rightHeightFinset (Q^(1/8:ℝ))
  let extra := big\small
  let F := rightPotential Q₀
  let G := finiteZeroPotential extra rightValue zeroMultiplicity
  have hlC : 0≤logCost := by dsimp [logCost]; positivity [Real.log_nonneg hQ₀.le]
  have hB : 0≤B := by dsimp [B]; positivity
  have hT2 : 2≤T := by
    dsimp [T]
    have h := Real.one_le_rpow hQ₀.le (by norm_num : (0:ℝ)≤1/8)
    linarith
  have hTQ : T≤Q^(1/6:ℝ) :=
    hTbound.trans (Real.rpow_le_rpow hQ₀p.le hQ₀Q (by norm_num))
  have hTb : T≤Q₀ := hTbound.trans
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ₀.le (by norm_num : (1/6:ℝ)≤1))
  have htRadio : Q^(1/8:ℝ)≤T := by
    refine (Real.rpow_le_rpow hQp.le hQupper (by norm_num : (0:ℝ)≤1/8)).trans ?_
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hQ₀p.le]
    dsimp only [T]
    have he : (2:ℝ)^(1/8:ℝ)≤2 := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (1/8:ℝ)≤1))
    exact mul_le_mul_of_nonneg_right he (by positivity)
  have hsub : small⊆big := right_height_mono (Real.rpow_le_rpow hQ₀p.le hQ₀Q (by norm_num))
  have htBig (r) (hr : r∈big) : |(rightValue r).im|≤T :=
    (show |(rightValue r).im|<Q^(1/8:ℝ) from (right_height_finite _).mem_toFinset.mp hr).le.trans htRadio
  have hlogle : (Real.log T)^5≤(Real.log Q₀)^5 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hTb) _
  have hmb : (∑ r∈big,zeroMultiplicity r*Q^((rightValue r).re-1))≤logCost :=
    (hCount big Q T (hQ₀.trans_le hQ₀Q) hT2 hTQ htBig).trans (mul_le_mul_of_nonneg_left hlogle hC)
  have hms : (∑ r∈small,zeroMultiplicity r*Q₀^((rightValue r).re-1))≤logCost :=
    (hCount small Q₀ T hQ₀ hT2 hTbound (fun r hr => htBig r (hsub hr))).trans
      (mul_le_mul_of_nonneg_left hlogle hC)
  have hm (r) : 0≤zeroMultiplicity r := by unfold zeroMultiplicity; positivity
  have hbeta (r : RightZero) : (rightValue r).re≤1 := r.val.property.1.2.le
  have hnr (r : RightZero) : rightValue r≠0 := fun h =>
    (ne_of_gt r.val.property.1.1) (by change (rightValue r).re=0; simp [h])
  have hFL (x) (hx : x∈Icc Q (2*Q)) (y) (hy : y∈Icc Q (2*Q)) :
      ‖F x-F y‖≤logCost*|x-y| := by
    exact (finite_zero_potential_lipschitz small rightValue zeroMultiplicity (fun r _ => hnr r)
      (fun r _ => hbeta r) (fun r _ => hm r) hQ₀p (hQ₀Q.trans hx.1) (hQ₀Q.trans hy.1)).trans
      ((mul_le_mul_of_nonneg_left hms (abs_nonneg _)).trans_eq (by ring))
  have hGL (x) (hx : x∈Icc Q (2*Q)) (y) (hy : y∈Icc Q (2*Q)) :
      ‖G x-G y‖≤B := by
    have he (r) (hr : r∈extra) : Q₀^(1/8:ℝ)≤|(rightValue r).im| :=
      le_of_not_gt (fun hh => (Finset.mem_sdiff.mp hr).2 ((right_height_finite _).mem_toFinset.mpr hh))
    have heSum : (∑ r∈extra,zeroMultiplicity r*Q^((rightValue r).re-1))≤logCost :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun r _ _ =>
        mul_nonneg (hm r) (Real.rpow_nonneg hQp.le _))).trans hmb
    exact (finite_zero_potential_high_height extra rightValue zeroMultiplicity
      (fun r _ => ⟨r.val.property.1.1.le,hbeta r⟩) (fun r _ => hm r) hQp hy hx
      (Real.rpow_pos_of_pos hQ₀p _) he).trans
        ((mul_le_mul_of_nonneg_left heSum (by positivity)).trans_eq (by dsimp [B]; ring))
  have heq : rightPotential Q = fun x => F x+G x := by
    ext x
    unfold rightPotential F G finiteZeroPotential
    rw [add_comm]
    exact (Finset.sum_sdiff hsub).symm
  refine ⟨?_,?_⟩
  · intro x hx y hy
    exact (finite_zero_potential_lipschitz big rightValue zeroMultiplicity (fun r _ => hnr r)
      (fun r _ => hbeta r) (fun r _ => hm r) hQp hy.1 hx.1).trans
      ((mul_le_mul_of_nonneg_left hmb (abs_nonneg _)).trans_eq (by ring))
  · intro a ha b hb hab
    let J := realDyadicMeshCount Q
    let R := realDyadicMeshRadius Q
    let H := realDyadicMeshWidth Q
    let u := realDyadicMeshPoint Q
    obtain ⟨hu,hu0,huJ,hw,_,hR,hRJ,hHJ⟩ := real_dyadic_mesh Q hQ
    have hJ : 0<J := hR.trans_le hRJ
    letI : NeZero J := ⟨hJ.ne'⟩
    have hH : 0≤H := Real.sqrt_nonneg _
    have hRlo : Q₀^(1/8:ℝ)≤(R:ℝ) :=
      (Real.rpow_le_rpow hQ₀p.le hQ₀Q (by norm_num)).trans (Nat.le_ceil _)
    have hRpos : (0:ℝ)<R := by exact_mod_cast hR
    have hQpower : Q₀/Q₀^(1/8:ℝ)=Q₀^(7/8:ℝ) := by
      have he : Q₀^(1:ℝ)/Q₀^(1/8:ℝ)=Q₀^(7/8:ℝ) := by
        rw [←Real.rpow_sub hQ₀p]
        norm_num
      simpa only [Real.rpow_one] using he
    have hHhi : H≤2*Q₀^(7/8:ℝ) := by
      have h := Real.sqrt_le_sqrt hQupper
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at h
      have h2 : Real.sqrt 2≤2 := (Real.sqrt_le_sqrt (by norm_num : (2:ℝ)≤2^2)).trans_eq
        (Real.sqrt_sq (by norm_num))
      have h3 : Real.sqrt Q₀ ≤ Q₀^(7/8:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hQ₀.le (by norm_num)
      exact h.trans (mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by norm_num))
    have hu0' : u 0=Q := hu0
    have huJ' : u J=2*Q := huJ
    have hcost := frozen_shell_row_error u hu hH hlC hB
      (show a∈Icc (u 0) (u J) by simpa only [hu0',huJ'] using ha)
      (show b∈Icc (u 0) (u J) by simpa only [hu0',huJ'] using hb)
      hab (fun j _ => hw j) F G
      (fun x hx y hy => hFL x (by simpa only [hu0',huJ'] using hx) y (by simpa only [hu0',huJ'] using hy))
      (fun x hx y hy => hGL x (by simpa only [hu0',huJ'] using hx) y (by simpa only [hu0',huJ'] using hy))
      R hR hRJ
    dsimp only [shellSpectrumRow]
    rw [dif_pos hJ,heq]
    refine hcost.trans ?_
    have hfirst : 12*logCost*H*(J:ℝ)/(R:ℝ)≤48*logCost*Q₀^(7/8:ℝ) := by
      calc
        _ ≤ (24*logCost*Q)/(R:ℝ) := by
          apply div_le_div_of_nonneg_right _ hRpos.le
          nlinarith only [mul_le_mul_of_nonneg_left hHJ hlC]
        _ ≤ (48*logCost*Q₀)/(R:ℝ) := by
          apply div_le_div_of_nonneg_right _ hRpos.le
          nlinarith only [mul_le_mul_of_nonneg_left hQupper hlC]
        _ ≤ (48*logCost*Q₀)/Q₀^(1/8:ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hRlo
        _ = _ := by rw [mul_div_assoc,hQpower]
    have hsecond : 2*B≤16*logCost*Q₀^(7/8:ℝ) := by
      dsimp only [B]
      rw [←mul_div_assoc]
      calc
        _ ≤ (16*logCost*Q₀)/Q₀^(1/8:ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith only [mul_le_mul_of_nonneg_left hQupper hlC]
        _ = _ := by rw [mul_div_assoc,hQpower]
    have hthird : 2*logCost*H≤4*logCost*Q₀^(7/8:ℝ) := by
      nlinarith only [mul_le_mul_of_nonneg_left hHhi hlC]
    have hh : 0≤logCost*Q₀^(7/8:ℝ) := by positivity
    dsimp [logCost] at *
    nlinarith only [hfirst,hsecond,hthird,hh]

end RHConnections.LongRankPhase
