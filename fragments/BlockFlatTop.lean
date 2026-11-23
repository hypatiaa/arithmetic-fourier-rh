import Verified

noncomputable section
namespace RHConnections.BlockFourier
open scoped BigOperators

variable {J : ℕ} [NeZero J]

def flatBand (b : ℤ) (k : ZMod J) : Prop :=
  ∃ i : ℤ, -b ≤ i ∧ i ≤ b ∧ (i : ZMod J) = k

def flatMask (b : ℤ) : Finset (ZMod J) :=
  (Finset.Icc (-b) b).image fun i : ℤ => (i : ZMod J)

omit [NeZero J] in
theorem mem_flatMask (b : ℤ) (k : ZMod J) : k ∈ flatMask b ↔ flatBand b k := by
  simp [flatMask, flatBand, Finset.mem_Icc, and_assoc]

def flatKernel (L : ZMod J → ℂ) (B : Finset (ZMod J)) (x : ZMod J) : ℂ :=
  (L x * ∑ q ∈ B, tone q x) / ((J : ℂ) * L 0)

private theorem dft_tone_product (L : ZMod J → ℂ) (k q : ZMod J) :
    ZMod.dft (fun x => L x * tone q x) k = ZMod.dft L (k - q) := by
  simp only [ZMod.dft_apply, smul_eq_mul, tone]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← mul_assoc, mul_right_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem flat_kernel_dft (L : ZMod J → ℂ) (B : Finset (ZMod J)) (k : ZMod J) :
    ZMod.dft (flatKernel L B) k =
      (∑ q ∈ B, ZMod.dft L (k - q)) / ((J : ℂ) * L 0) := by
  rw [show flatKernel L B = (fun x => (∑ q ∈ B, L x * tone q x) *
      ((J : ℂ) * L 0)⁻¹) by
    ext x
    simp [flatKernel, div_eq_mul_inv, Finset.mul_sum] ]
  rw [ZMod.dft_mul_const]
  have hs : (fun x => ∑ q ∈ B, L x * tone q x) =
      ∑ q ∈ B, (fun x => L x * tone q x) := by ext; simp [Finset.sum_apply]
  rw [hs, map_sum]
  simp [Finset.sum_apply, dft_tone_product, div_eq_mul_inv]

theorem flat_kernel_dft_one (L : ZMod J → ℂ) (B : Finset (ZMod J)) (k : ZMod J)
    (hL : L 0 ≠ 0) (hcover : ∀ q, q ∉ B → ZMod.dft L (k - q) = 0) :
    ZMod.dft (flatKernel L B) k = 1 := by
  rw [flat_kernel_dft, Finset.sum_subset (Finset.subset_univ B) (fun q _ => hcover q)]
  let e : ZMod J ≃ ZMod J :=
    { toFun := fun q => k - q
      invFun := fun q => k - q
      left_inv := fun q => sub_sub_cancel k q
      right_inv := fun q => sub_sub_cancel k q }
  have he := e.sum_comp (ZMod.dft L)
  change (∑ q, ZMod.dft L (k - q)) = _ at he
  rw [he]
  have hsum := congrFun (ZMod.dft_dft L) (0 : ZMod J)
  rw [ZMod.dft_apply] at hsum
  simp at hsum
  rw [hsum]
  exact div_self (mul_ne_zero (by exact_mod_cast NeZero.ne J) hL)

theorem flat_kernel_dft_zero (L : ZMod J → ℂ) (B : Finset (ZMod J)) (k : ZMod J)
    (hzero : ∀ q ∈ B, ZMod.dft L (k - q) = 0) :
    ZMod.dft (flatKernel L B) k = 0 := by
  rw [flat_kernel_dft, Finset.sum_eq_zero hzero, zero_div]

def jacksonFlatKernel (R m : ℕ) (x : ZMod J) : ℂ :=
  flatKernel (fun x => (smoothingKernel R x : ℂ)) (flatMask ((m : ℤ) + (2 * (R : ℤ) - 2))) x

theorem jackson_flat_dft_one {R m : ℕ} {k : ZMod J} (hR : 0 < R)
    (hk : flatBand (m : ℤ) k) : ZMod.dft (jacksonFlatKernel R m) k = 1 := by
  unfold jacksonFlatKernel
  apply flat_kernel_dft_one
  · have he : initialCharacterSum R (0 : ZMod J) = (R : ℂ) := by simp [initialCharacterSum, tone]
    have hp : 0 < smoothingKernel R (0 : ZMod J) := by
      rw [smoothingKernel, fourthWeight, he, Complex.norm_natCast]
      exact div_pos (by exact pow_pos (by exact_mod_cast hR) _) (normalizing_mass_positive hR)
    exact_mod_cast hp.ne'
  · intro q hq
    apply smoothing_kernel_dft_zero
    intro hm
    obtain ⟨a, ha₁, ha₂, ha⟩ := hk
    obtain ⟨b, hb₁, hb₂, hb⟩ := hm
    apply hq
    apply (mem_flatMask _ _).2
    refine ⟨a - b, by omega, by omega, ?_⟩
    rw [Int.cast_sub, ha, hb, sub_sub_cancel]

theorem jackson_flat_dft_zero {R m : ℕ} {k : ZMod J}
    (hk : ¬flatBand ((m : ℤ) + 4 * (R : ℤ) - 4) k) :
    ZMod.dft (jacksonFlatKernel R m) k = 0 := by
  unfold jacksonFlatKernel
  apply flat_kernel_dft_zero
  intro q hq
  apply smoothing_kernel_dft_zero
  intro hm
  obtain ⟨a, ha₁, ha₂, ha⟩ := (mem_flatMask _ _).1 hq
  obtain ⟨b, hb₁, hb₂, hb⟩ := hm
  apply hk
  refine ⟨b + a, by omega, by omega, ?_⟩
  rw [Int.cast_add, ha, hb, sub_add_cancel]

omit [NeZero J] in
theorem neg_mem_flatMask (b : ℤ) (q : ZMod J) :
    -q ∈ flatMask b ↔ q ∈ flatMask b := by
  simp only [mem_flatMask, flatBand]
  constructor <;> rintro ⟨i, hi₁, hi₂, hi⟩
  · exact ⟨-i, by omega, by omega, by simp [hi]⟩
  · exact ⟨-i, by omega, by omega, by simp [hi]⟩

def jacksonFlatReal (R m : ℕ) (x : ZMod J) : ℝ := (jacksonFlatKernel R m x).re

theorem ofReal_jackson_flat_real (R m : ℕ) (x : ZMod J) :
    (jacksonFlatReal R m x : ℂ) = jacksonFlatKernel R m x := by
  let B : Finset (ZMod J) := flatMask ((m : ℤ) + (2 * (R : ℤ) - 2))
  have hconj : (starRingEnd ℂ) (∑ q ∈ B, tone q x) = ∑ q ∈ B, tone q x := by
    rw [map_sum]
    simp only [tone, ← AddChar.map_neg_eq_conj, ← neg_mul]
    refine Finset.sum_bij' (fun q _ => -q) (fun q _ => -q) ?_ ?_ ?_ ?_ ?_
    · exact fun q hq => (neg_mem_flatMask _ q).2 hq
    · exact fun q hq => (neg_mem_flatMask _ q).2 hq
    · intros; simp
    · intros; simp
    · intros; rfl
  have hreal : (starRingEnd ℂ) (jacksonFlatKernel R m x) = jacksonFlatKernel R m x := by
    change (starRingEnd ℂ) (flatKernel _ B x) = flatKernel _ B x
    simp only [flatKernel, map_div₀, map_mul, map_natCast, Complex.conj_ofReal, hconj]
  have hi := congrArg Complex.im hreal
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · simp [jacksonFlatReal]
  · rw [Complex.ofReal_im]
    linarith

theorem jackson_flat_real_mass (R m : ℕ) (hR : 0 < R) :
    ∑ x : ZMod J, jacksonFlatReal R m x = 1 := by
  have hh := jackson_flat_dft_one (J := J) (R := R) (m := m) (k := 0) hR
    ⟨0, by omega, by omega, by simp⟩
  rw [ZMod.dft_apply] at hh
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul] at hh
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_one, ofReal_jackson_flat_real] using hh

open RHConnections.RankPairing in

theorem jackson_flat_first_moment (R m : ℕ) (hR : 0 < R) (hRJ : R ≤ J) (hm : m ≤ R) :
    (∑ x : ZMod J, ‖jacksonFlatKernel R m x‖ * (blockCyclicDistance x : ℝ)) ≤
      18 * (J : ℝ) / (R : ℝ) := by
  let B : Finset (ZMod J) := flatMask ((m : ℤ) + (2 * (R : ℤ) - 2))
  let A := normalizingMass (J := J) R
  have hA : 0 < A := normalizing_mass_positive hR
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hB : B.card ≤ 6 * R := by
    dsimp [B, flatMask]
    apply Finset.card_image_le.trans
    rw [Int.card_Icc]
    omega
  have he (x : ZMod J) : initialCharacterSum R x = blockDirichletKernel R x := rfl
  have hD (x : ZMod J) : ‖initialCharacterSum R x‖ ≤ (R : ℝ) := by
    unfold initialCharacterSum
    apply (norm_sum_le _ _).trans
    simp [tone, AddChar.norm_apply]
  have hAmax : A ≤ (J : ℝ) * (R : ℝ)^3 := by
    have hsum := block_dirichlet_second_moment (J := J) R hRJ
    calc
      A ≤ ∑ x : ZMod J, (R : ℝ)^2 * ‖blockDirichletKernel R x‖^2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [← he]
        unfold fourthWeight
        rw [show 4 = 2 + 2 by decide, pow_add]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hD x) 2) (by positivity)
      _ = _ := by rw [← Finset.mul_sum, hsum]; ring
  have hz : smoothingKernel R (0 : ZMod J) = (R : ℝ)^4 / A := by
    simp [smoothingKernel, fourthWeight, initialCharacterSum, tone, A]
  have hZ : (R : ℝ) ≤ (J : ℝ) * smoothingKernel R (0 : ZMod J) := by
    rw [hz, ← mul_div_assoc]
    apply (le_div_iff₀ hA).2
    calc
      _ ≤ (R : ℝ) * ((J : ℝ) * (R : ℝ)^3) :=
        mul_le_mul_of_nonneg_left hAmax hRr.le
      _ = _ := by ring
  have hden : 0 < (J : ℝ) * smoothingKernel R (0 : ZMod J) := hRr.trans_le hZ
  have hcardR : (B.card : ℝ) ≤ 6 * (R : ℝ) := by exact_mod_cast hB
  have hmask (x : ZMod J) : ‖∑ q ∈ B, tone q x‖ ≤ B.card := by
    apply (norm_sum_le _ _).trans
    simp [tone, AddChar.norm_apply]
  have hp (x : ZMod J) : ‖jacksonFlatKernel R m x‖ ≤ 6 * smoothingKernel R x := by
    change ‖(smoothingKernel R x : ℂ) * (∑ q ∈ B, tone q x) /
      ((J : ℂ) * (smoothingKernel R (0 : ZMod J) : ℂ))‖ ≤ _
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_natCast,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (smoothing_kernel_nonneg R x),
      abs_of_nonneg (smoothing_kernel_nonneg R (0 : ZMod J))]
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ smoothingKernel R x * (6 * (R : ℝ)) :=
        mul_le_mul_of_nonneg_left ((hmask x).trans hcardR) (smoothing_kernel_nonneg R x)
      _ ≤ smoothingKernel R x * (6 * ((J : ℝ) * smoothingKernel R 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ (by norm_num))
          (smoothing_kernel_nonneg R x)
      _ = _ := by ring
  calc
    _ ≤ ∑ x : ZMod J, (6 * smoothingKernel R x) * (blockCyclicDistance x : ℝ) := by
      exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hp x) (by positivity)
    _ = 6 * ∑ x : ZMod J, smoothingKernel R x * (blockCyclicDistance x : ℝ) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (jackson_circular_first_moment (J := J) R hR hRJ)
        (show (0 : ℝ) ≤ 6 by norm_num)
      convert hh using 1
      ring

open RHConnections.RankPairing in
theorem jackson_flat_real_first_moment (R m : ℕ) (hR : 0 < R) (hRJ : R ≤ J) (hm : m ≤ R) :
    (∑ x : ZMod J, |jacksonFlatReal R m x| * (blockCyclicDistance x : ℝ)) ≤
      18 * (J : ℝ) / (R : ℝ) := by
  have hnorm (x : ZMod J) : |jacksonFlatReal R m x| = ‖jacksonFlatKernel R m x‖ := by
    rw [← ofReal_jackson_flat_real, Complex.norm_real, Real.norm_eq_abs]
  simpa only [hnorm] using jackson_flat_first_moment (J := J) R m hR hRJ hm

end RHConnections.BlockFourier
