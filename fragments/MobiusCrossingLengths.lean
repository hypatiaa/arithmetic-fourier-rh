import Verified

noncomputable section
namespace RHConnections.MobiusCrossingLengths
open RankPairing ArithmeticFourierMertensKernel ArithmeticFourierInversion ArithmeticFourierShell

def paddedAt (N : ℕ) (S : Finset ℕ) (i : ℕ) :=
  if i < S.card then indexAt S i else N+1

theorem index_gap {S : Finset ℕ} {i j : ℕ} (hij : i ≤ j) (hj : j < S.card) :
    indexAt S i + (j-i) ≤ indexAt S j := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hj' : j < S.card := by omega
    have he : indexAt S j < indexAt S (j+1) := by
      simp only [indexAt,dite_eq_left hj',dite_eq_left hj]
      exact (S.orderIsoOfFin rfl).strictMono (show (⟨j,hj'⟩ : Fin S.card) < ⟨j+1,hj⟩ by exact Nat.lt_succ_self j)
    have h := ih hj'
    omega

theorem padded_prefix {N t i : ℕ} {S : Finset ℕ} (ht : t ≤ N) :
    paddedAt N S i ≤ t ↔ i < prefixCount S t := by
  have hc : prefixCount S t ≤ S.card := Finset.card_filter_le _ _
  by_cases hi : i < S.card
  · simpa [paddedAt,hi,prefixCount] using (prefix_membership_of_rank (t := t) hi)
  · simp only [paddedAt,ite_eq_right hi]
    omega

theorem crossing_iff {N t i : ℕ} {A B : Finset ℕ} (ht : t ≤ N) :
    paddedAt N A i ≤ t ∧ t < paddedAt N B i ↔
      prefixCount B t ≤ i ∧ i < prefixCount A t := by
  have hA := padded_prefix (i := i) (S := A) ht
  have hB := padded_prefix (i := i) (S := B) ht
  omega

theorem padded_length {N t j : ℕ} {A B : Finset ℕ} (ht : t ≤ N)
    (hj : j < prefixCount A t - prefixCount B t) :
    let i := prefixCount A t - 1 - j
    j+1 ≤ paddedAt N B i - paddedAt N A i := by
  let p := prefixCount A t
  let i := p-1-j
  have hp : p ≤ A.card := Finset.card_filter_le _ _
  have hlast : p-1 < A.card := by dsimp [p] at *; omega
  have hi : i < A.card := by dsimp [i,p] at *; omega
  have hl : indexAt A (p-1) ≤ t := (prefix_membership_of_rank hlast).2 (by change p-1 < p; dsimp [p] at *; omega)
  have hgap := index_gap (S := A) (i := i) (j := p-1) (Nat.sub_le _ _) hlast
  have ho : t < paddedAt N B i := by
    have he := padded_prefix (i := i) (S := B) ht
    dsimp [i,p] at *; omega
  change j+1 ≤ paddedAt N B i - paddedAt N A i
  rw [show paddedAt N A i = indexAt A i by simp [paddedAt,hi] ]
  dsimp [i,p] at *; omega

theorem genuine_length {N t i : ℕ} {A B : Finset ℕ}
    (hl : prefixCount B t ≤ i) (hu : i < prefixCount A t) (hg : i < B.card) :
    prefixCount A t - prefixCount B t ≤ paddedAt N B i - paddedAt N A i := by
  let p := prefixCount A t
  let q := prefixCount B t
  have hp : p ≤ A.card := Finset.card_filter_le _ _
  have hiA : i < A.card := hu.trans_le hp
  have hlast : p-1 < A.card := by change i < p at hu; omega
  have hleft := index_gap (S := A) (i := i) (j := p-1) (by change i < p at hu; omega) hlast
  have hright := index_gap (S := B) (i := q) (j := i) hl hg
  have hlo : indexAt A (p-1) ≤ t := (prefix_membership_of_rank hlast).2 (by change p-1<p; change i<p at hu; omega)
  have hq : q < B.card := lt_of_le_of_lt hl hg
  have hhi : t < indexAt B q := by
    have e := (prefix_membership_of_rank (t := t) hq)
    change (indexAt B q ≤ t ↔ q < q) at e
    omega
  simp only [paddedAt,ite_eq_left hiA,ite_eq_left hg]
  change p-q ≤ _
  change i < p at hu
  change q ≤ i at hl
  omega

theorem both_endpoint_gaps {N t i j : ℕ} {A B : Finset ℕ} (hij : i ≤ j)
    (hj : j < prefixCount A t) (hB : j < B.card) :
    paddedAt N A i + (j-i) ≤ paddedAt N A j ∧
    paddedAt N B i + (j-i) ≤ paddedAt N B j := by
  have hA := hj.trans_le (show prefixCount A t ≤ A.card from Finset.card_filter_le _ _)
  simp only [paddedAt,ite_eq_left hA,ite_eq_left hB,ite_eq_left (lt_of_le_of_lt hij hA),
    ite_eq_left (lt_of_le_of_lt hij hB)]
  exact ⟨index_gap hij hA,index_gap hij hB⟩

def squaredLengths (N t : ℕ) (A B : Finset ℕ) : ℕ :=
  ∑ j ∈ Finset.range (prefixCount A t - prefixCount B t),
    (paddedAt N B (prefixCount A t-1-j) - paddedAt N A (prefixCount A t-1-j))^2

private theorem squares (m : ℕ) :
    m*(m+1)*(2*m+1) = 6 * ∑ j ∈ Finset.range m, (j+1)^2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,Nat.mul_add 6,← ih]; ring

theorem padded_cubic {N t : ℕ} (ht : t ≤ N) (A B : Finset ℕ) :
    let m := prefixCount A t - prefixCount B t
    m*(m+1)*(2*m+1) ≤ 6*squaredLengths N t A B := by
  dsimp only
  rw [squares]
  apply Nat.mul_le_mul_left
  exact Finset.sum_le_sum (fun j hj => Nat.pow_le_pow_left (padded_length (A := A) (B := B) ht (Finset.mem_range.mp hj)) 2)

def crossingCount (N t : ℕ) : ℕ :=
  max (prefixCount (positivePositions N) t) (prefixCount (negativePositions N) t) -
  min (prefixCount (positivePositions N) t) (prefixCount (negativePositions N) t)

theorem crossingCount_abs {N t : ℕ} (ht : t ≤ N) : (crossingCount N t : ℝ) = |M t| := by
  rw [← prefix_rank_imbalance ht]
  unfold crossingCount
  rw [Nat.cast_sub (by omega)]
  by_cases h : prefixCount (positivePositions N) t ≤ prefixCount (negativePositions N) t
  · rw [max_eq_right h,min_eq_left h,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · have h' := le_of_not_ge h
    rw [max_eq_left h',min_eq_right h',abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h'))]

theorem mobius_squared_crossing_lengths {N t : ℕ} (ht : t ≤ N) :
    let P := positivePositions N
    let V := negativePositions N
    let m := crossingCount N t
    m*(m+1)*(2*m+1) ≤ 6*(squaredLengths N t P V + squaredLengths N t V P) := by
  dsimp only
  let p := prefixCount (positivePositions N) t
  let v := prefixCount (negativePositions N) t
  change (max p v-min p v)*(max p v-min p v+1)*(2*(max p v-min p v)+1) ≤ _
  by_cases h : p ≤ v
  · have e := padded_cubic ht (negativePositions N) (positivePositions N)
    change (v-p)*(v-p+1)*(2*(v-p)+1) ≤ _ at e
    rw [max_eq_right h,min_eq_left h]
    exact e.trans (Nat.mul_le_mul_left 6 (Nat.le_add_left _ _))
  · have h' := le_of_not_ge h
    have e := padded_cubic ht (positivePositions N) (negativePositions N)
    change (p-v)*(p-v+1)*(2*(p-v)+1) ≤ _ at e
    rw [max_eq_left h',min_eq_right h']
    exact e.trans (Nat.mul_le_mul_left 6 (Nat.le_add_right _ _))

theorem quarter_separation {N t j k : ℕ} {A B : Finset ℕ}
    (hj : j < (prefixCount A t-prefixCount B t)/4)
    (hk : prefixCount A t-prefixCount B t-(prefixCount A t-prefixCount B t)/4 ≤ k)
    (hku : k < prefixCount A t-prefixCount B t) (hreal : prefixCount B t+k < B.card) :
    let m := prefixCount A t-prefixCount B t
    let q := prefixCount B t
    paddedAt N A (q+j)+m/2 ≤ paddedAt N A (q+k) ∧
    paddedAt N B (q+j)+m/2 ≤ paddedAt N B (q+k) := by
  dsimp only
  have h := both_endpoint_gaps (N := N) (t := t) (A := A) (B := B)
    (i := prefixCount B t+j) (j := prefixCount B t+k) (by omega) (by omega) hreal
  omega

theorem terminal_unit_length {N : ℕ} {A B : Finset ℕ}
    (hi : B.card ≤ A.card-1) (ha : 0 < A.card) (he : indexAt A (A.card-1) = N) :
    paddedAt N B (A.card-1)-paddedAt N A (A.card-1) = 1 := by
  simp [paddedAt,not_lt.mpr hi,show A.card-1 < A.card by omega,he]

end RHConnections.MobiusCrossingLengths
