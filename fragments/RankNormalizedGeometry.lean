import Verified

noncomputable section
open Set
namespace RHConnections.MobiusCrossingLengths

theorem normalized_reciprocal_gap {t x y m : ℝ} (ht : 0<t)
    (hx : 0<x) (hy : 0<y) (hxU : x≤9*t/8) (hyU : y≤9*t/8)
    (hm : 0≤m) (hsep : m≤y-x) :
    m/(2*t)≤t/x-t/y := by
  have he : t/x-t/y=t*(y-x)/(x*y) := by field_simp <;> ring
  rw [he]
  have hxy : x*y≤2*t^2 := by
    have h := mul_le_mul hxU hyU hy.le (by linarith)
    nlinarith only [h,sq_nonneg t]
  calc
    _ = t*m/(2*t^2) := by field_simp <;> ring
    _ ≤ t*m/(x*y) := div_le_div_of_nonneg_left (by positivity) (by positivity) hxy
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsep ht.le) (by positivity)

theorem normalized_endpoint_near_one {t x ε : ℝ} (ht : 0<t)
    (hε : 0≤ε) (hε1 : ε≤1/2) (h : |x-t|≤ε*t) :
    0<x ∧ |t/x-1|≤2*ε := by
  have hlow : t/2≤x := by
    have h1 := (abs_le.mp h).1
    have h2 := mul_le_mul_of_nonneg_right hε1 ht.le
    linarith
  have hp : 0<x := by linarith
  refine ⟨hp,?_⟩
  rw [show t/x-1=(t-x)/x by field_simp,abs_div,abs_of_pos hp,abs_sub_comm]
  exact (div_le_div_of_nonneg_right h hp.le).trans
    ((div_le_div_of_nonneg_left (by positivity) (by positivity) hlow).trans_eq (by field_simp <;> ring))

theorem normalized_endpoint_in_shell {Q L t x : ℝ} (hQ : 0<Q) (ht : 0<t)
    (hL : L∈Icc (3*Q/2) (7*Q/4)) (hx : x∈Icc (7*t/8) (9*t/8)) :
    L*(t/x)∈Icc Q (2*Q) := by
  have hx0 : 0<x := by linarith [hx.1]
  have hL0 : 0<L := by linarith [hL.1]
  rw [Set.mem_Icc,←mul_div_assoc]
  constructor
  · apply (le_div_iff₀ hx0).mpr
    have h₁ := mul_le_mul_of_nonneg_left hx.2 hQ.le
    have h₂ := mul_le_mul_of_nonneg_right hL.1 ht.le
    nlinarith only [h₁,h₂,mul_pos hQ ht]
  · apply (div_le_iff₀ hx0).mpr
    have h₁ := mul_le_mul_of_nonneg_left hx.1 (by positivity : 0≤2*Q)
    have h₂ := mul_le_mul_of_nonneg_right hL.2 ht.le
    nlinarith only [h₁,h₂]

def firstQuarterRanks (q m : ℕ) : Finset ℕ := Finset.Ico q (q+m/4)

def lastQuarterRanks (q m : ℕ) : Finset ℕ := Finset.Ico (q+m-m/4) (q+m)

theorem cardinal_first_quarter (q m : ℕ) : (firstQuarterRanks q m).card=m/4 := by
  rw [firstQuarterRanks,Nat.card_Ico,Nat.add_sub_cancel_left]

theorem cardinal_last_quarter (q m : ℕ) : (lastQuarterRanks q m).card=m/4 := by
  rw [lastQuarterRanks,Nat.card_Ico]
  omega

theorem first_last_quarter_sizes {q m : ℕ} (hm : 8≤m) :
    ((m:ℝ)/8≤(firstQuarterRanks q m).card) ∧ ((m:ℝ)/8≤(lastQuarterRanks q m).card) := by
  rw [cardinal_first_quarter,cardinal_last_quarter]
  have hh : m≤8*(m/4) := by omega
  have hr : (m:ℝ)≤8*((m/4:ℕ):ℝ) := by exact_mod_cast hh
  exact ⟨by linarith,by linarith⟩

end RHConnections.MobiusCrossingLengths
