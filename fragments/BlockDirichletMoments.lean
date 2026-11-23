import Verified
import BlockDirichletBound

noncomputable section
namespace RHConnections.RankPairing
open scoped BigOperators

private theorem block_char_sum {J : ℕ} [NeZero J] (u : ZMod J) :
    (∑ h : ZMod J, ZMod.stdAddChar (u * h)) = if u = 0 then (J : ℂ) else 0 := by
  split_ifs with hu
  · simp [hu, ZMod.card]
  · simpa only [AddChar.mulShift_apply] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar J hu)

private theorem block_char_conj {J : ℕ} [NeZero J] (u : ZMod J) :
    (starRingEnd ℂ) (ZMod.stdAddChar u) = ZMod.stdAddChar (-u) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

private theorem block_moment_count {J : ℕ} [NeZero J] {ι : Type*} (S : Finset ι)
    (f : ι → ZMod J) [DecidableEq ι] :
    (∑ h : ZMod J, ‖∑ i ∈ S, ZMod.stdAddChar (f i * h)‖ ^ 2) =
      (J : ℝ) * ↑(((S ×ˢ S).filter fun p => f p.1 = f p.2).card) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  have hexpand (h : ZMod J) :
      (↑(‖∑ i ∈ S, ZMod.stdAddChar (f i * h)‖ ^ 2) : ℂ) =
        ∑ p ∈ S ×ˢ S, ZMod.stdAddChar ((f p.1 - f p.2) * h) := by
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [block_char_conj, ← AddChar.map_add_eq_mul, sub_mul, sub_eq_add_neg]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  simp_rw [block_char_sum, sub_eq_zero]
  push_cast
  rw [← Finset.sum_boole (fun p : ι × ι => f p.1 = f p.2) (S ×ˢ S), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases heq : f p.1 = f p.2 <;> simp [heq]

theorem block_dirichlet_second_moment {J : ℕ} [NeZero J] (R : ℕ) (hR : R ≤ J) :
    (∑ h : ZMod J, ‖blockDirichletKernel R h‖ ^ 2) = (J : ℝ) * R := by
  rw [show (∑ h : ZMod J, ‖blockDirichletKernel R h‖ ^ 2) =
      _ from block_moment_count (Finset.range R) (fun i => (i : ZMod J))]
  have hcard : (((Finset.range R ×ˢ Finset.range R).filter
      fun p => (p.1 : ZMod J) = (p.2 : ZMod J)).card) = R := by
    rw [Finset.card_filter, Finset.sum_product]
    calc
      _ = ∑ a ∈ Finset.range R, ∑ b ∈ Finset.range R, (if b = a then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        have haJ := (Finset.mem_range.mp ha).trans_le hR
        have hbJ := (Finset.mem_range.mp hb).trans_le hR
        have he : (a : ZMod J) = (b : ZMod J) ↔ b = a := by
          constructor
          · intro hab
            have hv := congrArg ZMod.val hab
            rw [ZMod.val_natCast_of_lt haJ, ZMod.val_natCast_of_lt hbJ] at hv
            exact hv.symm
          · rintro rfl
            rfl
        simp [he]
      _ = R := by
        simp only [Finset.sum_ite_eq', Finset.mem_range]
        rw [← Finset.card_filter]
        simp only [Finset.filter_true_of_mem (fun a ha => Finset.mem_range.mp ha),
          Finset.card_range]
  rw [hcard]

theorem block_dirichlet_fourth_moment_lower {J : ℕ} [NeZero J] (R : ℕ) (hR : 1 ≤ R) :
    (J : ℝ) * (R : ℝ)^3 / 27 ≤ ∑ h : ZMod J, ‖blockDirichletKernel R h‖ ^ 4 := by
  let S := Finset.range R ×ˢ Finset.range R
  let f (p : ℕ × ℕ) : ZMod J := (p.1 : ZMod J) + (p.2 : ZMod J)
  let F := (S ×ˢ S).filter fun p => f p.1 = f p.2
  have hs (h : ZMod J) : (blockDirichletKernel R h)^2 =
      ∑ p ∈ S, ZMod.stdAddChar (f p * h) := by
    rw [pow_two, blockDirichletKernel, Finset.sum_mul_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [← AddChar.map_add_eq_mul, show f (a,b) * h =
      (a : ZMod J) * h + (b : ZMod J) * h by simp [f, add_mul] ]
  have hmoment : (∑ h : ZMod J, ‖blockDirichletKernel R h‖ ^ 4) = (J : ℝ) * F.card := by
    rw [← block_moment_count S f]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← hs, norm_pow]
    ring
  let K := (R + 2) / 3
  let T := Finset.Icc (K - 1) (2 * K - 2)
  let g (p : ℕ × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
    ((p.1, p.2.1), (p.2.2, p.1 + p.2.1 - p.2.2))
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hi : (T ×ˢ (T ×ˢ T)).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn g
    · intro p hp
      have ⟨ha, hb, hc⟩ :
          (K - 1 ≤ p.1 ∧ p.1 ≤ 2 * K - 2) ∧
          (K - 1 ≤ p.2.1 ∧ p.2.1 ≤ 2 * K - 2) ∧
          (K - 1 ≤ p.2.2 ∧ p.2.2 ≤ 2 * K - 2) := by
        simpa only [Finset.mem_coe, Finset.mem_product, T, Finset.mem_Icc] using hp
      have hdc : p.2.2 ≤ p.1 + p.2.1 := by omega
      rw [Finset.mem_coe, Finset.mem_filter]
      constructor
      · simp only [g, S, Finset.mem_product, Finset.mem_range]
        dsimp [K] at *
        omega
      · simp only [g, f]
        rw [← Nat.cast_add, ← Nat.cast_add]
        congr 1
        omega
    · intro p hp q hq heq
      have ha := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.1.1) heq
      have hb := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.1.2) heq
      have hc := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.2.1) heq
      exact Prod.ext ha (Prod.ext hb hc)
  have hT : T.card = K := by dsimp [T]; rw [Nat.card_Icc]; omega
  simp only [Finset.card_product, hT] at hi
  have hr : (R : ℝ) ≤ 3 * (K : ℝ) := by
    exact_mod_cast (show R ≤ 3 * K by dsimp [K]; omega)
  have hc : (K : ℝ)^3 ≤ F.card := by
    exact_mod_cast (show K^3 ≤ F.card by simpa [pow_succ, mul_assoc] using hi)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) R) hr 3
  rw [mul_pow] at hp
  norm_num at hp
  rw [hmoment]
  calc
    _ = (J : ℝ) * ((R : ℝ)^3 / 27) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hp, hc]) (by positivity)

end RHConnections.RankPairing
