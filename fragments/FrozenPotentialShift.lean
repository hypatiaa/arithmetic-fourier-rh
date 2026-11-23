import Verified

noncomputable section
namespace RHConnections.LongRankPhase
open RHConnections.PhaseWindow RHConnections.LocalModeContrast

theorem right_potential_frozen_lipschitz (hIngham : ZetaDensityPremise) :
    ∃ C : ℝ, 0≤C ∧ ∀ q : ℝ, 1<q → 2*q^(1/8:ℝ)≤q^(1/6:ℝ) →
      ∀ x y : ℝ, q≤x → q≤y →
        ‖rightPotential q x-rightPotential q y‖≤C*(Real.log q)^5*|x-y| := by
  obtain ⟨C,hC,hcount⟩ := weighted_right_finset hIngham
  refine ⟨C,hC,?_⟩
  intro q hq ht x y hx hy
  let T := 2*q^(1/8:ℝ)
  let S := rightHeightFinset (q^(1/8:ℝ))
  have hq0 : 0<q := zero_lt_one.trans hq
  have hT : 2≤T := by
    dsimp [T]
    linarith [Real.one_le_rpow hq.le (by norm_num : (0:ℝ)≤1/8)]
  have hTq : T≤q := ht.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq.le (by norm_num : (1/6:ℝ)≤1))
  have hHeight (r : RightZero) (hr : r∈S) : |(rightValue r).im|≤T := by
    have hr' : |(rightValue r).im|<q^(1/8:ℝ) := (right_height_finite _).mem_toFinset.mp hr
    dsimp [T]
    linarith [Real.rpow_nonneg hq0.le (1/8:ℝ)]
  have hMass := hcount S q T hq hT ht hHeight
  have hLog := pow_le_pow_left₀ (Real.log_nonneg (show 1≤T by linarith))
    (Real.log_le_log (show 0<T by linarith) hTq) 5
  have hMass' : (∑ r∈S,zeroMultiplicity r*q^((rightValue r).re-1))≤C*(Real.log q)^5 :=
    hMass.trans (mul_le_mul_of_nonneg_left hLog hC)
  have hnonzero (r : RightZero) : rightValue r≠0 := by
    intro hr
    have hp : 0<(rightValue r).re := r.val.property.1.1
    simp [hr] at hp
  refine (finite_zero_potential_lipschitz S rightValue zeroMultiplicity
    (fun r _ => hnonzero r) (fun r _ => r.val.property.1.2.le)
    (fun r _ => by unfold zeroMultiplicity; positivity) hq0 hx hy).trans ?_
  exact (mul_le_mul_of_nonneg_left hMass' (abs_nonneg _)).trans_eq (by ring)

theorem frozen_interval_change_bound (F : ℝ → ℂ) {q D A B a b a' b' : ℝ}
    (hD : 0≤D) (hF : ∀ x y : ℝ, q≤x → q≤y → ‖F x-F y‖≤D*|x-y|)
    (ha : q≤a) (hb : q≤b) (ha' : q≤a') (hb' : q≤b')
    (haMove : |a-a'|≤A) (hbMove : |b-b'|≤B) :
    ‖(F b-F a)-(F b'-F a')‖≤D*(A+B) := by
  rw [show F b-F a-(F b'-F a')= (F b-F b')-(F a-F a') by ring]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((hF b b' hb hb').trans (mul_le_mul_of_nonneg_left hbMove hD))
    ((hF a a' ha ha').trans (mul_le_mul_of_nonneg_left haMove hD))).trans_eq ?_
  ring

end RHConnections.LongRankPhase
