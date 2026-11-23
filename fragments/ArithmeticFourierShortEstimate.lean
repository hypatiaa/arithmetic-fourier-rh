import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks
open ArithmeticFourierInversion

theorem centered_finite_bound {ι : Type*} (I : Finset ι) (b f : ι → ℝ)
    (s D : ℝ) (hD : 0 ≤ D) (hb : ∀ q ∈ I, 0 ≤ b q)
    (hf : ∀ q ∈ I, |f q-s| ≤ D) :
    let m := ∑ q ∈ I, (b q-1)
    |∑ q ∈ I, (b q-1)*f q| ≤ |m| * |s|+(2*I.card+|m|)*D := by
  let m := ∑ q ∈ I, (b q-1)
  have ht : (∑ q ∈ I, |b q-1|) ≤ 2*I.card+|m| := by
    calc
      _ ≤ ∑ q ∈ I, (b q+1) := Finset.sum_le_sum fun q hq =>
        (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hb q hq),abs_one])
      _ = 2*I.card + m := by simp [m,Finset.sum_add_distrib,Finset.sum_sub_distrib]; ring
      _ ≤ _ := add_le_add (le_refl _) (le_abs_self m)
  change |∑ q ∈ I, (b q-1)*f q| ≤ _
  have he : (∑ q ∈ I, (b q-1)*f q) = m*s + ∑ q ∈ I, (b q-1)*(f q-s) := by
    rw [show m*s = ∑ q ∈ I, (b q-1)*s from Finset.sum_mul ..,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he]
  calc
    _ ≤ |m*s|+|∑ q ∈ I, (b q-1)*(f q-s)| := abs_add_le _ _
    _ ≤ |m| * |s|+∑ q ∈ I, |b q-1| * D := by
      rw [abs_mul]
      apply add_le_add (le_refl _)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun q hq => by rw [abs_mul]; gcongr; exact hf q hq
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right ht hD)

private theorem quotient_motion (X Q H q : ℕ) (hQ : 0 < Q) (hL : Q ≤ q)
    (hU : q ≤ Q+H) :
    ((X/Q:ℕ):ℝ)-((X/q:ℕ):ℝ) ≤ 1+(X:ℝ)*H/(Q:ℝ)^2 := by
  have hq : 0 < q := hQ.trans_le hL
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hLr : (Q:ℝ) ≤ q := by exact_mod_cast hL
  have hUr : (q:ℝ) ≤ (Q:ℝ)+H := by exact_mod_cast hU
  have hdiv : ((X/Q:ℕ):ℝ) ≤ (X:ℝ)/Q := by
    apply (le_div_iff₀ hQr).mpr
    exact_mod_cast (Nat.div_mul_le_self X Q)
  have hfloor : (X:ℝ)/q ≤ ((X/q:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hqr).mpr
    have hmod : ((X%q:ℕ):ℝ) ≤ (q:ℝ) := by exact_mod_cast (Nat.mod_lt X hq).le
    have hcast : (q:ℝ)*((X/q:ℕ):ℝ)+((X%q:ℕ):ℝ) = X := by
      exact_mod_cast Nat.div_add_mod X q
    nlinarith only [hcast,hmod]
  have hrat : (X:ℝ)/Q-(X:ℝ)/q ≤ (X:ℝ)*H/(Q:ℝ)^2 := by
    have hfact : (X:ℝ)/Q-(X:ℝ)/q = (X:ℝ)*((q:ℝ)-Q)/((Q:ℝ)*q) := by
      field_simp
    rw [hfact]
    have hx : (0:ℝ) ≤ X := Nat.cast_nonneg _
    calc
      _ ≤ (X:ℝ)*H/((Q:ℝ)*q) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hUr]) hx) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by
        rw [pow_two]; exact mul_le_mul_of_nonneg_left hLr hQr.le)
  linarith only [hdiv,hfloor,hrat]

def shortWeight (B : ℕ) (q : ℕ) : ℝ := vonMangoldt q * (1-g B q)

theorem short_weight_nonneg (B q : ℕ) : 0 ≤ shortWeight B q := by
  apply mul_nonneg vonMangoldt_nonneg
  rw [sub_nonneg,g_apply]
  split_ifs
  · by_cases h : q = 0
    · simp [h]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
  · norm_num

theorem short_block_bound (F b : ℕ → ℝ)
    (hF : ∀ l r : ℕ, l ≤ r → |F r-F l| ≤ (r:ℝ)-l)
    (X Q H : ℕ) (hQ : 0<Q)
    (hb : ∀ q ∈ Finset.Ioc Q (Q+H), 0 ≤ b q) :
    let I := Finset.Ioc Q (Q+H)
    let m := ∑ q ∈ I,(b q-1)
    |∑ q ∈ I,(b q-1)*F (X/q)| ≤
      |m| * |F (X/Q)|+(2*(H:ℝ)+|m|)*(1+(X:ℝ)*H/(Q:ℝ)^2) := by
  let D : ℝ := 1+(X:ℝ)*H/(Q:ℝ)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have h := centered_finite_bound (Finset.Ioc Q (Q+H)) b (fun q => F (X/q)) (F (X/Q)) D hD hb
    (fun q hq => by
      obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hq
      rw [abs_sub_comm]
      exact (hF _ _ (Nat.div_le_div_left hl.le hQ)).trans (quotient_motion X Q H q hQ hl.le hu))
  simpa only [Nat.card_Ioc,Nat.add_sub_cancel_left,D] using h

theorem scalar_short_block_bound (B X Q H : ℕ) (hQ : 0<Q) :
    let I := Finset.Ioc Q (Q+H)
    let m := ∑ q ∈ I,(shortWeight B q-1)
    |∑ q ∈ I,(shortWeight B q-1)*S B (X/q)| ≤
      |m| * |S B (X/Q)|+(2*(H:ℝ)+|m|)*(1+(X:ℝ)*H/(Q:ℝ)^2) :=
  short_block_bound (S B) (shortWeight B) (scalar_S_lipschitz B) X Q H hQ
    (fun q _ => short_weight_nonneg B q)

theorem mertens_short_block_bound (X Q H : ℕ) (hQ : 0<Q) :
    let I := Finset.Ioc Q (Q+H)
    let m := ∑ q ∈ I,(vonMangoldt q-1)
    |∑ q ∈ I,(vonMangoldt q-1)*M (X/q)| ≤
      |m| * |M (X/Q)|+(2*(H:ℝ)+|m|)*(1+(X:ℝ)*H/(Q:ℝ)^2) :=
  short_block_bound M vonMangoldt mertens_M_lipschitz X Q H hQ
    (fun _ _ => vonMangoldt_nonneg)

end RHConnections.ArithmeticFourierShortBlocks
