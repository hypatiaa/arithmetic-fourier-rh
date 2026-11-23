import Verified
import ZetaConjugateMultiplicity

noncomputable section
open Filter
namespace RHConnections.LongRankPhase
open PhaseWindow SpectralTail LocalModeContrast BlockFourier

private def rightConjugate (r : RightZero) : RightZero :=
  ⟨conjugateZeroEquiv r.val,by simpa only [conjugateZeroEquiv_val,Complex.conj_re] using r.property⟩

private theorem right_conjugate_involutive : Function.Involutive rightConjugate := by
  intro r
  apply Subtype.ext
  apply Subtype.ext
  simp [rightConjugate]

private def rightConjugateEquiv : RightZero ≃ RightZero :=
  ⟨rightConjugate,rightConjugate,right_conjugate_involutive,right_conjugate_involutive⟩

theorem right_potential_conjugate (Q x : ℝ) :
    (starRingEnd ℂ) (rightPotential Q x)=rightPotential Q x := by
  let s := rightHeightFinset (Q^(1/8:ℝ))
  let F (r : RightZero) := (zeroMultiplicity r:ℂ)*zeroPrimitive (rightValue r) x
  let e := rightConjugateEquiv
  have hmem (r : RightZero) : e r∈s ↔ r∈s := by
    dsimp [s,rightHeightFinset]
    simp only [Set.Finite.mem_toFinset]
    change |(rightValue (rightConjugate r)).im|<_ ↔ |(rightValue r).im|<_
    simp [rightConjugate,rightValue]
  have hmap : s.map e.toEmbedding=s := by
    ext r
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp h
      exact (hmem u).mpr hu
    · intro hr
      refine Finset.mem_map.mpr ⟨e.symm r,?_,e.apply_symm_apply r⟩
      apply (hmem (e.symm r)).mp
      rwa [e.apply_symm_apply]
  change (starRingEnd ℂ) (∑ r∈s,F r)=∑ r∈s,F r
  rw [map_sum]
  calc
    _ = ∑ r∈s,F (e r) := by
      apply Finset.sum_congr rfl
      intro r _
      change (starRingEnd ℂ) (F r)=F (rightConjugate r)
      have hord : analyticOrderNatAt riemannZeta ((starRingEnd ℂ) r.val.val) =
          analyticOrderNatAt riemannZeta r.val.val := conjugateZeroEquiv_order r.val
      simp [F,rightConjugate,zeroMultiplicity,zeroPrimitive,rightValue,
        ←Complex.exp_conj,map_div₀,hord]
    _ = _ := by
      change (∑ r∈s,F (e.toEmbedding r))=_
      rw [←Finset.sum_map,hmap]

theorem long_row_value_conjugate (X Q : ℝ) (r : RankRow) :
    (starRingEnd ℂ) (longRowValue X Q r)=longRowValue X Q r := by
  dsimp only [longRowValue]
  split_ifs <;> try simp only [_root_.map_zero]
  simp only [complexIntervalSum,smoothComplexPositive,shellBlockSignal,map_sum,map_mul,map_sub,
    Complex.conj_ofReal,right_potential_conjugate]

theorem projected_real_center_cost_le (X Q : ℝ) (c : ℂ) :
    longRowCost X Q (c.re:ℂ)≤longRowCost X Q c := by
  unfold longRowCost
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro r _
  have hnonneg := nonnegative_row_weight r
  apply mul_le_mul_of_nonneg_left _ hnonneg
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have hV := (Complex.conj_eq_iff_im.mp (long_row_value_conjugate X Q r))
  let len : ℝ := (rowStartLength X Q r).2
  let V := longRowValue X Q r
  change ‖V-(c.re:ℂ)*(len:ℂ)‖≤‖V-c*(len:ℂ)‖
  have he : V-(c.re:ℂ)*(len:ℂ)=((V-c*(len:ℂ)).re:ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im,V,hV]
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem uniform_real_center_iff (eta delta : ℝ) :
    UniformLongRowPower eta delta ↔
      ∃ C : ℝ, 0≤C ∧ ∀ᶠ X : ℝ in atTop, ∃ c : ℝ,
        longRowCost X (X^eta) (c:ℂ) ≤ C*Real.sqrt (⌊X/(X^eta)⌋₊:ℝ)*(X^eta)^(1-delta) := by
  constructor
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,h.mono (fun X ⟨c,hc⟩ => ⟨c.re,
      (projected_real_center_cost_le X (X^eta) c).trans hc⟩)⟩
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,h.mono (fun _ ⟨c,hc⟩ => ⟨(c:ℂ),hc⟩)⟩

theorem uniform_natural_real_center_iff (eta delta : ℝ) :
    UniformNaturalLongRowPower eta delta ↔
      ∃ C : ℝ, 0≤C ∧ ∀ᶠ n : ℕ in atTop, ∃ c : ℝ,
        let X := (n:ℝ)
        longRowCost X (X^eta) (c:ℂ) ≤ C*Real.sqrt (⌊X/(X^eta)⌋₊:ℝ)*(X^eta)^(1-delta) := by
  constructor
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,h.mono (fun n ⟨c,hc⟩ => ⟨c.re,
      (projected_real_center_cost_le n ((n:ℝ)^eta) c).trans hc⟩)⟩
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,h.mono (fun _ ⟨c,hc⟩ => ⟨(c:ℂ),hc⟩)⟩

end RHConnections.LongRankPhase
