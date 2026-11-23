import Verified

noncomputable section
namespace RHConnections.RankPairing

def realDyadicMeshWidth (Q : ℝ) : ℝ := Real.sqrt Q

def realDyadicMeshCount (Q : ℝ) : ℕ := ⌈realDyadicMeshWidth Q⌉₊

def realDyadicMeshPoint (Q : ℝ) (j : ℕ) : ℝ :=
  min (2 * Q) (Q + (j : ℝ) * realDyadicMeshWidth Q)

def realDyadicMeshRadius (Q : ℝ) : ℕ := ⌈Q ^ (1 / 8 : ℝ)⌉₊

theorem real_dyadic_mesh (Q : ℝ) (hQ : 1 ≤ Q) :
    let H := realDyadicMeshWidth Q
    let J := realDyadicMeshCount Q
    let u := realDyadicMeshPoint Q
    let R := realDyadicMeshRadius Q
    Monotone u ∧ u 0 = Q ∧ u J = 2 * Q ∧
      (∀ j, u (j + 1) - u j ≤ H) ∧
      (∀ j ≤ J, |u j - (Q + (j : ℝ) * H)| ≤ H) ∧
      0 < R ∧ R ≤ J ∧ H * (J : ℝ) ≤ 2 * Q := by
  let H := realDyadicMeshWidth Q
  let J := realDyadicMeshCount Q
  let u := realDyadicMeshPoint Q
  let R := realDyadicMeshRadius Q
  have hQ0 : 0 ≤ Q := by linarith
  have hH : 1 ≤ H := by
    exact (Real.le_sqrt (by norm_num) hQ0).2 (by simpa using hQ)
  have hH0 : 0 ≤ H := by linarith
  have hHsq : H * H = Q := by
    simpa [H, realDyadicMeshWidth, pow_two] using Real.sq_sqrt hQ0
  have hJlo : H ≤ (J : ℝ) := Nat.le_ceil H
  have hJhi : (J : ℝ) ≤ H + 1 := (Nat.ceil_lt_add_one hH0).le
  have hmul_lo : Q ≤ (J : ℝ) * H := by
    rw [← hHsq]
    exact mul_le_mul_of_nonneg_right hJlo hH0
  have hmul_hi : (J : ℝ) * H ≤ Q + H := by
    calc
      _ ≤ (H + 1) * H := mul_le_mul_of_nonneg_right hJhi hH0
      _ = Q + H := by rw [add_mul, hHsq, one_mul]
  have hu (j : ℕ) : u j = min (2 * Q) (Q + (j : ℝ) * H) := rfl
  change Monotone u ∧ u 0 = Q ∧ u J = 2 * Q ∧
      (∀ j, u (j + 1) - u j ≤ H) ∧
      (∀ j ≤ J, |u j - (Q + (j : ℝ) * H)| ≤ H) ∧
      0 < R ∧ R ≤ J ∧ H * (J : ℝ) ≤ 2 * Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hu, hu]
    exact min_le_min_left _ (add_le_add_right
      (mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) hH0) _)
  · rw [hu, Nat.cast_zero, zero_mul, add_zero, min_eq_right (by linarith)]
  · rw [hu, min_eq_left (by linarith only [hmul_lo])]
  · intro j
    rw [hu, hu, Nat.cast_succ]
    by_cases hj : Q + (j : ℝ) * H ≤ 2 * Q
    · rw [min_eq_right hj]
      have hh := min_le_right (2 * Q) (Q + ((j : ℝ) + 1) * H)
      nlinarith only [hh]
    · have hj' : 2 * Q ≤ Q + (j : ℝ) * H := (lt_of_not_ge hj).le
      rw [min_eq_left hj']
      have hh := min_le_left (2 * Q) (Q + ((j : ℝ) + 1) * H)
      linarith only [hh, hH0]
  · intro j hj
    rw [hu]
    by_cases hj' : Q + (j : ℝ) * H ≤ 2 * Q
    · rw [min_eq_right hj', sub_self, abs_zero]
      exact hH0
    · have hj'' : 2 * Q ≤ Q + (j : ℝ) * H := (lt_of_not_ge hj').le
      rw [min_eq_left hj'', abs_of_nonpos (sub_nonpos.mpr hj'')]
      have hh := (mul_le_mul_of_nonneg_right
        (show (j : ℝ) ≤ J by exact_mod_cast hj) hH0).trans hmul_hi
      linarith only [hh]
  · have hp : 0 < Q ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hr : (0 : ℝ) < R := hp.trans_le (Nat.le_ceil _)
    exact_mod_cast hr
  · apply Nat.ceil_mono
    rw [realDyadicMeshWidth, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
  · rw [mul_comm]
    have hh : H ≤ H * H := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hH hH0
    linarith only [hmul_hi, hh, hHsq]

end RHConnections.RankPairing
