import Verified

open Filter
noncomputable section
namespace RHConnections.SpectralTail

theorem zeta_inverse_three_halves_with_multiplicity :
    Summable (fun r : NontrivialZetaZero =>
      (analyticOrderNatAt riemannZeta r.val : ℝ)/(‖r.val‖ * Real.sqrt ‖r.val‖)) := by
  classical
  obtain ⟨C, hC, hcount⟩ := zeta_quantitative_zero_count
  obtain ⟨δ, hδ, hd⟩ := zeta_zero_norm_lower
  let N (T : ℝ) := C*(max T 1+2)*Real.log (max T 1+2)
  let A := 8*C*Real.log 2
  let B := max 1 (δ * Real.sqrt δ)⁻¹
  let q : ℝ := (2 * Real.sqrt 2)⁻¹
  let m := fun r : NontrivialZetaZero => analyticOrderNatAt riemannZeta r.val
  let S (j : ℕ) := {r : NontrivialZetaZero | heightBin r.val.im = j}
  let f (r : NontrivialZetaZero) := (m r : ℝ)/(‖r.val‖ * Real.sqrt ‖r.val‖)
  have hq : 0 < q := by dsimp [q]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hbin (r : NontrivialZetaZero) (j : ℕ) (hj : heightBin r.val.im = j) :
      (‖r.val‖ * Real.sqrt ‖r.val‖)⁻¹ ≤ B*q^j := by
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero, mul_one]
      exact (inv_anti₀ (by positivity : 0 < δ * Real.sqrt δ)
        (mul_le_mul (hd r) (Real.sqrt_le_sqrt (hd r)) (Real.sqrt_nonneg _) (norm_nonneg _))).trans
        (le_max_right _ _)
    have hpow : (2 : ℝ)^j ≤ ‖r.val‖ := by
      simpa only [hj] using (heightBin_lower r.val.im (by rw [hj]; exact hj0)).trans (Complex.abs_im_le_norm _)
    have hsq : (Real.sqrt 2 ^ j)^2 = (2 : ℝ)^j := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hs : Real.sqrt 2 ^ j ≤ Real.sqrt ‖r.val‖ :=
      (Real.le_sqrt (by positivity) (norm_nonneg _)).2 (by rw [hsq]; exact hpow)
    have hp : (2 * Real.sqrt 2)^j ≤ ‖r.val‖ * Real.sqrt ‖r.val‖ := by
      rw [mul_pow]
      exact mul_le_mul hpow hs (by positivity) (norm_nonneg _)
    calc
      _ ≤ ((2 * Real.sqrt 2)^j)⁻¹ := inv_anti₀ (by positivity) hp
      _ = q^j := by simp only [q, inv_pow]
      _ ≤ B*q^j := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (pow_nonneg hq.le j)
  have hc (j : ℕ) (s : Finset NontrivialZetaZero)
      (hs : ∀ r ∈ s, |r.val.im| < (2:ℝ)^(j+1)) :
      (∑ r ∈ s, (m r : ℝ)) ≤ A*((j:ℝ)+1)*2^j := by
    apply le_trans _ (cumulative_count_dyadic N C hC (fun T hT => by simp [N, max_eq_left hT]) j)
    exact hcount (max ((2:ℝ)^(j+1)) 1) s (le_max_right _ _)
      (fun r hr => (hs r hr).le.trans (le_max_left _ _))
  have hf : 0 ≤ f := fun r => by dsimp [f]; positivity
  have hpart (r : NontrivialZetaZero) : ∃! j, r ∈ S j :=
    ⟨heightBin r.val.im, rfl, fun _ h => (show heightBin r.val.im = _ from h).symm⟩
  let major (j : ℕ) := (A*B)*(((j:ℝ)+1)*(2*q)^j)
  have hsum (j : ℕ) (s : Finset (S j)) : (∑ r ∈ s, f r) ≤ major j := by
    let e : S j ↪ NontrivialZetaZero := ⟨Subtype.val, Subtype.val_injective⟩
    have hm := hc j (s.map e) (by
      intro r hr
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hr
      change |k.val.val.im| < (2:ℝ)^(j+1)
      have hk : heightBin k.val.val.im = j := k.property
      simpa only [hk] using heightBin_upper k.val.val.im)
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

theorem zeta_inverse_three_halves_repeated :
    Summable (fun r : RepeatedZetaZero => 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)) := by
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using
    zeta_inverse_three_halves_with_multiplicity

#print axioms zeta_inverse_three_halves_with_multiplicity
#print axioms zeta_inverse_three_halves_repeated
end RHConnections.SpectralTail
