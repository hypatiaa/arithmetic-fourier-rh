import Verified
import ArithmeticFourierRankBandwidth

open ArithmeticFunction
noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierDyadic ArithmeticFourierMertensKernel ArithmeticFourierInversion

theorem quotient_cutoff_spacing (X Q a b : ℕ) (hQ : 0 < Q) (ha : Q ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2*Q) :
    (X:ℝ)*((b:ℝ)-(a:ℝ))/(4*(Q:ℝ)^2)-1 ≤ ((X/a:ℕ):ℝ)-((X/b:ℕ):ℝ) := by
  have ha0 : 0 < a := hQ.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hAr : (0:ℝ) < a := by exact_mod_cast ha0
  have hBr : (0:ℝ) < b := by exact_mod_cast hb0
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have huB : (b:ℝ) ≤ 2*(Q:ℝ) := by exact_mod_cast hb
  have hAB : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hfloorB : ((X/b:ℕ):ℝ) ≤ (X:ℝ)/b := by
    apply (le_div_iff₀ hBr).mpr
    exact_mod_cast Nat.div_mul_le_self X b
  have hfloorA : (X:ℝ)/a ≤ ((X/a:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hAr).mpr
    have hmod : ((X%a:ℕ):ℝ) ≤ (a:ℝ) := by exact_mod_cast (Nat.mod_lt X ha0).le
    have he : (a:ℝ)*((X/a:ℕ):ℝ)+((X%a:ℕ):ℝ)=X := by exact_mod_cast Nat.div_add_mod X a
    nlinarith only [he,hmod]
  have habprod : (a:ℝ)*(b:ℝ) ≤ 4*(Q:ℝ)^2 := by
    calc
      _ ≤ (2*(Q:ℝ))*(2*(Q:ℝ)) := mul_le_mul (hAB.trans huB) huB hBr.le (by positivity)
      _ = _ := by ring
  have hfrac : (X:ℝ)*((b:ℝ)-(a:ℝ))/(4*(Q:ℝ)^2) ≤ (X:ℝ)/a-(X:ℝ)/b := by
    rw [show (X:ℝ)/a-(X:ℝ)/b = (X:ℝ)*((b:ℝ)-(a:ℝ))/((a:ℝ)*(b:ℝ)) by field_simp]
    exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hAB))
      (mul_pos hAr hBr) habprod
  linarith only [hfrac,hfloorA,hfloorB]

theorem dyadic_rank_banded_cost (X Q r H w : ℕ) (hQ : 0 < Q)
    (u : ℕ → ℕ) (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q)
    (hspacing : ∀ i < r, ∀ j < r, i ≤ j → H*(j-i) ≤ u j-u i)
    (B : ℝ) (hB : 0 ≤ B) (hM : ∀ j < r, |M (X/u j)| ≤ B)
    (hgap : 8*B+4*((X/Q).sqrt:ℝ)+1 ≤ (X:ℝ)*(H:ℝ)*((w:ℝ)+1)/(4*(Q:ℝ)^2)) :
    let N := X/Q
    let K := blockKernel (Finset.range r) u (blockVM u) X
    sqNorm N (actualResidual N K) ≤ B*(2*(w:ℝ)+1)*(∑ j ∈ Finset.range r,(blockVM u j)^2) := by
  let N := X/Q
  let t := fun j => X/u j
  have hu0 (j : ℕ) : Q ≤ u j := h0 ▸ hu (Nat.zero_le _)
  have hur (j : ℕ) (hj : j < r) : u j ≤ 2*Q := hr ▸ hu hj.le
  have htl (j : ℕ) (_ : j < r) : t j ≤ N := Nat.div_le_div_left (hu0 _) hQ
  have hordered (i j : ℕ) (hi : i < r) (hj : j < r) (hij : i+w < j) :
      8*B+4*(N.sqrt:ℝ) ≤ ((t i-t j:ℕ):ℝ) := by
    have hij' : i ≤ j := by omega
    have htij : t j ≤ t i := Nat.div_le_div_left (hu hij') (hQ.trans_le (hu0 _))
    have hdist := quotient_cutoff_spacing X Q (u i) (u j) hQ (hu0 i) (hu hij') (hur j hj)
    have hHnat : H*(w+1) ≤ u j-u i :=
      (Nat.mul_le_mul_left H (show w+1 ≤ j-i by omega)).trans (hspacing i hi j hj hij')
    have hHr : (H:ℝ)*((w:ℝ)+1) ≤ (u j:ℝ)-(u i:ℝ) := by
      rw [← Nat.cast_sub (hu hij')]
      exact_mod_cast hHnat
    have hscaled := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHr (Nat.cast_nonneg X))
      (show 0 ≤ (4:ℝ)*(Q:ℝ)^2 by positivity)
    rw [← mul_assoc] at hscaled
    rw [Nat.cast_sub htij]
    change _ ≤ ((X/u i:ℕ):ℝ)-((X/u j:ℕ):ℝ)
    linarith only [hgap,hscaled,hdist]
  have hfar (i : ℕ) (hi : i < r) (j : ℕ) (hj : j < r) (hnot : j∉indexBand r w i) :
      8*B+4*(N.sqrt:ℝ) ≤ ((max (t i) (t j)-min (t i) (t j):ℕ):ℝ) := by
    have hd := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,h⟩)
    by_cases hsep : i+w < j
    · have htii : t j ≤ t i := Nat.div_le_div_left (hu (by omega : i ≤ j)) (hQ.trans_le (hu0 _))
      simpa only [max_eq_left htii,min_eq_right htii] using hordered i j hi hj hsep
    · have hsep' : j+w < i := lt_of_not_ge (fun hle => hd ⟨hle,le_of_not_gt hsep⟩)
      have htii : t i ≤ t j := Nat.div_le_div_left (hu (by omega : j ≤ i)) (hQ.trans_le (hu0 _))
      simpa only [max_eq_right htii,min_eq_left htii] using hordered j i hj hi hsep'
  have hresult := rank_banded_cutoff_cost N r w t (blockVM u) B hB htl hM hfar
  have he : (fun n => ∑ j ∈ Finset.range r,blockVM u j*cutoffStep (t j) n) =
      blockKernel (Finset.range r) u (blockVM u) X := by
    ext n
    simp [blockKernel,cutoffStep,t,mul_ite]
  rw [he] at hresult
  exact hresult

end RHConnections.RankPairing
