import Verified

open Filter
noncomputable section
namespace RHConnections.SpectralTail

variable {ι : Type*} (rho : ι → ℂ) (m : ι → ℕ)
    {δ C : ℝ} (hδ : 0 < δ) (hd : ∀ i, δ ≤ ‖rho i‖) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), 1 ≤ T →
      (∀ i ∈ s, |(rho i).im| ≤ T) →
      (∑ i ∈ s, (m i : ℝ)) ≤ C*(T+2)*Real.log (T+2))

include hδ hd hC hcount

theorem inverse_three_halves_with_multiplicity :
    Summable (fun r : ι => (m r : ℝ)/(‖rho r‖ * Real.sqrt ‖rho r‖)) := by
  classical
  let N (T : ℝ) := C*(max T 1+2)*Real.log (max T 1+2)
  let A := 8*C*Real.log 2
  let B := max 1 (δ * Real.sqrt δ)⁻¹
  let q : ℝ := (2 * Real.sqrt 2)⁻¹
  let S (j : ℕ) := {r : ι | heightBin (rho r).im = j}
  let f (r : ι) := (m r : ℝ)/(‖rho r‖ * Real.sqrt ‖rho r‖)
  have hq : 0 < q := by dsimp [q]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hbin (r : ι) (j : ℕ) (hj : heightBin (rho r).im = j) :
      (‖rho r‖ * Real.sqrt ‖rho r‖)⁻¹ ≤ B*q^j := by
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero, mul_one]
      exact (inv_anti₀ (by positivity : 0 < δ * Real.sqrt δ)
        (mul_le_mul (hd r) (Real.sqrt_le_sqrt (hd r)) (Real.sqrt_nonneg _) (norm_nonneg _))).trans
        (le_max_right _ _)
    have hpow : (2 : ℝ)^j ≤ ‖rho r‖ := by
      simpa only [hj] using (heightBin_lower (rho r).im (by rw [hj]; exact hj0)).trans (Complex.abs_im_le_norm (rho r))
    have hsq : (Real.sqrt 2 ^ j)^2 = (2 : ℝ)^j := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hs : Real.sqrt 2 ^ j ≤ Real.sqrt ‖rho r‖ :=
      (Real.le_sqrt (by positivity) (norm_nonneg _)).2 (by rw [hsq]; exact hpow)
    have hp : (2 * Real.sqrt 2)^j ≤ ‖rho r‖ * Real.sqrt ‖rho r‖ := by
      rw [mul_pow]
      exact mul_le_mul hpow hs (by positivity) (norm_nonneg _)
    calc
      _ ≤ ((2 * Real.sqrt 2)^j)⁻¹ := inv_anti₀ (by positivity) hp
      _ = q^j := by simp only [q, inv_pow]
      _ ≤ B*q^j := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (pow_nonneg hq.le j)
  have hc (j : ℕ) (s : Finset ι)
      (hs : ∀ r ∈ s, |(rho r).im| < (2:ℝ)^(j+1)) :
      (∑ r ∈ s, (m r : ℝ)) ≤ A*((j:ℝ)+1)*2^j := by
    apply le_trans _ (cumulative_count_dyadic N C hC (fun T hT => by simp [N, max_eq_left hT]) j)
    exact hcount (max ((2:ℝ)^(j+1)) 1) s (le_max_right _ _)
      (fun r hr => (hs r hr).le.trans (le_max_left _ _))
  have hf : 0 ≤ f := fun r => by dsimp [f]; positivity
  have hpart (r : ι) : ∃! j, r ∈ S j :=
    ⟨heightBin (rho r).im, rfl, fun _ h => (show heightBin (rho r).im = _ from h).symm⟩
  let major (j : ℕ) := (A*B)*(((j:ℝ)+1)*(2*q)^j)
  have hsum (j : ℕ) (s : Finset (S j)) : (∑ r ∈ s, f r) ≤ major j := by
    let e : S j ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
    have hm := hc j (s.map e) (by
      intro r hr
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hr
      change |(rho k.val).im| < (2:ℝ)^(j+1)
      have hk : heightBin (rho k.val).im = j := k.property
      simpa only [hk] using heightBin_upper (rho k.val).im)
    simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk] at hm
    calc
      _ ≤ ∑ r ∈ s, (m r : ℝ)*(B*q^j) := by
        apply Finset.sum_le_sum
        intro r _
        dsimp only [f]; rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (hbin r j r.property) (Nat.cast_nonneg _)
      _ = (∑ r ∈ s, (m r : ℝ))*(B*q^j) := (Finset.sum_mul ..).symm
      _ ≤ (A*((j:ℝ)+1)*2^j)*(B*q^j) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg (zero_le_one.trans hB) (pow_nonneg hq.le _))
      _ = major j := by dsimp only [major]; rw [mul_pow]; ring
  have hsqrt : 1 < Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hr : ‖2*q‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2*q)]
    dsimp only [q]
    rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity : 0 < 2 * Real.sqrt 2)]
    linarith
  have hgeom : Summable (fun j : ℕ => ((j:ℝ)+1)*(2*q)^j) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr).add
      (summable_geometric_of_norm_lt_one hr)
    simpa only [pow_one, add_mul, one_mul, Pi.add_apply] using h
  have hinner (j : ℕ) : Summable (fun r : S j => f r) :=
    summable_of_sum_le (fun r => hf r) (hsum j)
  apply (summable_partition hf hpart).2
  refine ⟨hinner, (hgeom.mul_left (A*B)).of_nonneg_of_le
    (fun j => tsum_nonneg (fun r => hf r)) (fun j => ?_)⟩
  exact le_of_tendsto (hinner j).hasSum (Eventually.of_forall (hsum j))

theorem inverse_three_halves_repeated :
    Summable (fun r : (Σ i : ι, Fin (m i)) => 1/(‖rho r.1‖ * Real.sqrt ‖rho r.1‖)) := by
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using
    inverse_three_halves_with_multiplicity rho m hδ hd hC hcount

#print axioms inverse_three_halves_with_multiplicity
#print axioms inverse_three_halves_repeated
end RHConnections.SpectralTail
