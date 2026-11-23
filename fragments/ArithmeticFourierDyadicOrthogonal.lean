import Verified

open scoped RealInnerProductSpace
noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierDyadic ArithmeticFourierMertensKernel ArithmeticFourierInversion

theorem separated_cutoff_residual_cost (N r : ℕ) (t : ℕ → ℕ) (d : ℕ → ℝ) (B : ℝ)
    (ht : ∀ j < r, t j ≤ N) (hM : ∀ j < r, |M (t j)| ≤ B)
    (hgap : ∀ i < r, ∀ j < r, i < j →
      8 * B + 4 * (N.sqrt : ℝ) ≤ ((t i - t j : ℕ) : ℝ))
    (hmono : Antitone t) :
    sqNorm N (actualResidual N (fun n => ∑ j ∈ Finset.range r, d j * cutoffStep (t j) n)) =
      ∑ j ∈ Finset.range r, (d j)^2 * sqNorm N (actualResidual N (cutoffStep (t j))) := by
  let V := fun j => residualVector N (cutoffStep (t j))
  have horth (i : ℕ) (hi : i < r) (j : ℕ) (hj : j < r) (hne : i ≠ j) :
      ⟪V i, V j⟫ = 0 := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · dsimp only [V]
      rw [real_inner_comm, residual_inner_eq_dot]
      exact actual_cutoff_gram_zero_of_spacing (hmono hij.le) (ht i hi) (hM j hj) (hM i hi)
        (hgap i hi j hj hij)
    · dsimp only [V]
      rw [residual_inner_eq_dot]
      exact actual_cutoff_gram_zero_of_spacing (hmono hji.le) (ht j hj) (hM i hi) (hM j hj)
        (hgap j hj i hi hji)
  have he : (∑ j ∈ Finset.range r, d j • V j) =
      residualVector N (fun n => ∑ j ∈ Finset.range r, d j * cutoffStep (t j) n) := by
    have hf : (fun n => ∑ j ∈ Finset.range r, d j * cutoffStep (t j) n) =
        ∑ j ∈ Finset.range r, d j • cutoffStep (t j) := by
      ext n
      simp [Finset.sum_apply]
    rw [hf, map_sum]
    simp only [map_smul, V]
  have h := orthogonal_weighted_cost r V d horth
  rw [he, norm_rank_residual, Real.sq_sqrt (sqNorm_nonneg _ _)] at h
  simp only [V, norm_rank_residual, Real.sq_sqrt (sqNorm_nonneg _ _)] at h
  exact h

theorem dyadic_zero_band_spacing (X Q H : ℕ) (hQ : 0 < Q) (B : ℝ)
    (_hB : 0 ≤ B)
    (hH : 4 * (Q : ℝ) * (8 * B + 4 * ((X / Q).sqrt : ℝ) + 1) ≤
      ((X / Q : ℕ) : ℝ) * H) :
    8 * B + 4 * ((X / Q).sqrt : ℝ) + 1 ≤
      (X : ℝ) * (H : ℝ) / (4 * (Q : ℝ)^2) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNQ : ((X / Q : ℕ) : ℝ) * (Q : ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X Q
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ = (4 * (Q : ℝ) * (8 * B + 4 * ((X / Q).sqrt : ℝ) + 1)) * Q := by ring
    _ ≤ (((X / Q : ℕ) : ℝ) * H) * Q := mul_le_mul_of_nonneg_right hH hQr.le
    _ = (((X / Q : ℕ) : ℝ) * Q) * H := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hNQ (Nat.cast_nonneg H)

theorem dyadic_rank_orthogonal_cost (X Q r H : ℕ) (hQ : 0 < Q)
    (u : ℕ → ℕ) (hu : Monotone u) (h0 : u 0 = Q) (hr : u r = 2 * Q)
    (hspacing : ∀ i < r, ∀ j < r, i < j → H ≤ u j - u i)
    (B : ℝ) (hB : 0 ≤ B) (hM : ∀ j < r, |M (X / u j)| ≤ B)
    (hH : 4 * (Q : ℝ) * (8 * B + 4 * ((X / Q).sqrt : ℝ) + 1) ≤
      ((X / Q : ℕ) : ℝ) * H) :
    let N := X / Q
    let K := blockKernel (Finset.range r) u (blockVM u) X
    sqNorm N (actualResidual N K) =
      ∑ j ∈ Finset.range r, (blockVM u j)^2 *
        sqNorm N (actualResidual N (cutoffStep (X / u j))) := by
  let t := fun j => X / u j
  have hu0 (j : ℕ) : Q ≤ u j := h0 ▸ hu (Nat.zero_le j)
  have hur (j : ℕ) (hj : j < r) : u j ≤ 2 * Q := hr ▸ hu hj.le
  have ht : Antitone t := fun i j hij => Nat.div_le_div_left (hu hij) (hQ.trans_le (hu0 i))
  have htN (j : ℕ) (_ : j < r) : t j ≤ X / Q := Nat.div_le_div_left (hu0 j) hQ
  have hs (i : ℕ) (hi : i < r) (j : ℕ) (hj : j < r) (hij : i < j) :
      8 * B + 4 * ((X / Q).sqrt : ℝ) ≤ ((t i - t j : ℕ) : ℝ) := by
    have hdist := quotient_cutoff_spacing X Q (u i) (u j) hQ (hu0 i) (hu hij.le) (hur j hj)
    have hHr : (H : ℝ) ≤ (u j : ℝ) - (u i : ℝ) := by
      rw [← Nat.cast_sub (hu hij.le)]
      exact_mod_cast hspacing i hi j hj hij
    have hscaled := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHr (Nat.cast_nonneg X))
      (show 0 ≤ (4 : ℝ) * (Q : ℝ)^2 by positivity)
    have hthreshold := dyadic_zero_band_spacing X Q H hQ B hB hH
    rw [Nat.cast_sub (ht hij.le)]
    change _ ≤ ((X/u i : ℕ) : ℝ) - ((X/u j : ℕ) : ℝ)
    linarith only [hthreshold, hscaled, hdist]
  have he : (fun n => ∑ j ∈ Finset.range r, blockVM u j * cutoffStep (t j) n) =
      blockKernel (Finset.range r) u (blockVM u) X := by
    ext n
    simp [blockKernel, cutoffStep, t, mul_ite]
  simpa only [he] using
    separated_cutoff_residual_cost (X / Q) r t (blockVM u) B htN hM hs ht

theorem dyadic_rank_orthogonal_bound (X Q r H : ℕ) (hQ : 0 < Q)
    (u : ℕ → ℕ) (hu : Monotone u) (h0 : u 0 = Q) (hr : u r = 2 * Q)
    (hspacing : ∀ i < r, ∀ j < r, i < j → H ≤ u j - u i)
    (B D : ℝ) (hB : 0 ≤ B) (hM : ∀ j < r, |M (X / u j)| ≤ B)
    (hH : 4 * (Q : ℝ) * (8 * B + 4 * ((X / Q).sqrt : ℝ) + 1) ≤
      ((X / Q : ℕ) : ℝ) * H)
    (hD : 0 ≤ D) (hcoeff : ∀ j < r, |blockVM u j| ≤ D * (H : ℝ)) :
    let N := X / Q
    let K := blockKernel (Finset.range r) u (blockVM u) X
    sqNorm N (actualResidual N K) ≤
      B * (D * H) * ((2 * (Real.log 4 + 4) + 1) * Q) := by
  dsimp only
  rw [dyadic_rank_orthogonal_cost X Q r H hQ u hu h0 hr hspacing B hB hM hH]
  calc
    _ ≤ ∑ j ∈ Finset.range r, (B * (D * H)) * |blockVM u j| := by
      apply Finset.sum_le_sum
      intro j hj
      have hlt := Finset.mem_range.mp hj
      have ht : X / u j ≤ X / Q := Nat.div_le_div_left (h0 ▸ hu (Nat.zero_le j)) hQ
      have hc := (rank_step_cost_le_mertens (X / Q) (X / u j) ht).trans (hM j hlt)
      calc
        _ ≤ (blockVM u j)^2 * B := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
        _ = (|blockVM u j| * |blockVM u j|) * B := by rw [← pow_two, sq_abs]
        _ ≤ ((D * H) * |blockVM u j|) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcoeff j hlt) (abs_nonneg _)) hB
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (dyadic_block_discrepancy_l1 Q r u hu h0 hr)
        (by positivity)

theorem dyadic_rounded_spacing (N Q : ℕ) (hN : 0 < N) (B : ℝ)
    (hroot : (N.sqrt : ℝ) ≤ B) (hB : 1 ≤ B)
    (hscale : 1 ≤ (Q : ℝ) * B / (N : ℝ)) :
    let H := ⌈4 * (Q : ℝ) * (8 * B + 4 * (N.sqrt : ℝ) + 1) / (N : ℝ)⌉₊
    4 * (Q : ℝ) * (8 * B + 4 * (N.sqrt : ℝ) + 1) ≤ (N : ℝ) * H ∧
      (H : ℝ) ≤ 53 * (Q : ℝ) * B / (N : ℝ) := by
  let x := 4 * (Q : ℝ) * (8 * B + 4 * (N.sqrt : ℝ) + 1) / (N : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · have hh := (div_le_iff₀ hNr).1 (Nat.le_ceil x)
    simpa only [mul_comm (⌈x⌉₊ : ℝ) (N : ℝ)] using hh
  · have htop : x ≤ 52 * (Q : ℝ) * B / (N : ℝ) := by
      dsimp [x]
      apply div_le_div_of_nonneg_right _ hNr.le
      calc
        _ ≤ 4 * (Q : ℝ) * (13 * B) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by ring
    have hu := (Nat.ceil_lt_add_one hx).le
    change (⌈x⌉₊ : ℝ) ≤ _
    rw [show 53 * (Q : ℝ) * B / (N : ℝ) =
      52 * (Q : ℝ) * B / (N : ℝ) + (Q : ℝ) * B / (N : ℝ) by ring]
    linarith only [htop, hu, hscale]

theorem orthogonal_rank_power_transfer (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q)
    (E B T A c C : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T) (hA : 0 < A)
    (hc : 0 < c) (hC : 0 ≤ C)
    (hrange : Real.log (Q : ℝ) ≤ A * Real.sqrt (Real.log (N : ℝ)))
    (hM : B ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ))))
    (hE : E ≤ T * (B * (Q : ℝ) / Real.sqrt (N : ℝ))^2) :
    Real.sqrt E ≤ Real.sqrt T * C * Real.sqrt (N : ℝ) * (Q : ℝ)^(1 - c / A) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hex : Real.exp (-c * Real.sqrt (Real.log (N : ℝ))) ≤ (Q : ℝ)^(-c / A) := by
    rw [Real.rpow_def_of_pos hQr]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hrange (show 0 ≤ c / A by positivity)
    rw [show c / A * (A * Real.sqrt (Real.log (N : ℝ))) =
      c * Real.sqrt (Real.log (N : ℝ)) by field_simp] at hh
    rw [neg_div]
    linarith
  have hq : 0 ≤ B * (Q : ℝ) / Real.sqrt (N : ℝ) := by positivity
  have hfactor : B * (Q : ℝ) / Real.sqrt (N : ℝ) ≤
      C * Real.sqrt (N : ℝ) * (Q : ℝ)^(1 - c / A) := by
    rw [show 1 - c / A = 1 + (-c / A) by ring, Real.rpow_add hQr, Real.rpow_one]
    apply (div_le_iff₀ hsN).2
    have hh := mul_le_mul_of_nonneg_right
      (hM.trans (mul_le_mul_of_nonneg_left hex (by positivity : 0 ≤ C * (N : ℝ)))) hQr.le
    calc
      _ ≤ (C * (N : ℝ) * (Q : ℝ)^(-c / A)) * Q := hh
      _ = C * (Real.sqrt (N : ℝ))^2 * (Q : ℝ)^(-c / A) * Q := by rw [Real.sq_sqrt hNr.le]
      _ = _ := by ring
  refine (Real.sqrt_le_sqrt hE).trans ?_
  rw [Real.sqrt_mul hT, Real.sqrt_sq hq]
  exact (mul_le_mul_of_nonneg_left hfactor (Real.sqrt_nonneg T)).trans_eq (by ring)

theorem dyadic_rank_orthogonal_restricted_power (X Q r H : ℕ)
    (hQ : 0 < Q) (hN : 0 < X / Q)
    (u : ℕ → ℕ) (hu : Monotone u) (h0 : u 0 = Q) (hr : u r = 2 * Q)
    (hspacing : ∀ i < r, ∀ j < r, i < j → H ≤ u j - u i)
    (B D S A c C : ℝ) (hB : 0 ≤ B) (hM : ∀ j < r, |M (X / u j)| ≤ B)
    (hH : 4 * (Q : ℝ) * (8 * B + 4 * ((X / Q).sqrt : ℝ) + 1) ≤
      ((X / Q : ℕ) : ℝ) * H)
    (hD : 0 ≤ D) (hcoeff : ∀ j < r, |blockVM u j| ≤ D * (H : ℝ))
    (hS : 0 ≤ S) (hmesh : (H : ℝ) ≤ S * (Q : ℝ) * B / ((X / Q : ℕ) : ℝ))
    (hA : 0 < A) (hc : 0 < c) (hC : 0 ≤ C)
    (hrange : Real.log (Q : ℝ) ≤ A * Real.sqrt (Real.log ((X / Q : ℕ) : ℝ)))
    (hEnv : B ≤ C * ((X / Q : ℕ) : ℝ) *
      Real.exp (-c * Real.sqrt (Real.log ((X / Q : ℕ) : ℝ)))) :
    let N := X / Q
    let K := blockKernel (Finset.range r) u (blockVM u) X
    Real.sqrt (sqNorm N (actualResidual N K)) ≤
      Real.sqrt (D * S * (2 * (Real.log 4 + 4) + 1)) * C *
        Real.sqrt (N : ℝ) * (Q : ℝ)^(1 - c / A) := by
  dsimp only
  let N := X / Q
  let T := 2 * (Real.log 4 + 4) + 1
  have hT : 0 ≤ T := by
    have hh : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp [T]
    linarith
  apply orthogonal_rank_power_transfer N Q hN hQ _ B (D * S * T) A c C
    hB (by positivity) hA hc hC hrange hEnv
  refine (dyadic_rank_orthogonal_bound X Q r H hQ u hu h0 hr hspacing
    B D hB hM hH hD hcoeff).trans ?_
  change B * (D * H) * (T * (Q : ℝ)) ≤ _
  calc
    _ ≤ B * (D * (S * (Q : ℝ) * B / (N : ℝ))) * (T * (Q : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmesh hD) hB) (by positivity)
    _ = _ := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
      ring

end RHConnections.RankPairing
