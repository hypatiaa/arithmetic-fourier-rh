import Verified

noncomputable section
open Set
namespace RHConnections.RankContrast
open RankPairing MobiusRankLocalization MobiusCrossingLengths

def lowerEndpoint (t i : ℕ) := min (indexAt (signSet true (2*t)) i) (indexAt (signSet false (2*t)) i)
def upperEndpoint (t i : ℕ) := max (indexAt (signSet true (2*t)) i) (indexAt (signSet false (2*t)) i)
def normalizedA (t i : ℕ) : ℝ := (t:ℝ)/upperEndpoint t i
def normalizedB (t i : ℕ) : ℝ := (t:ℝ)/lowerEndpoint t i

theorem actual_normalized_window {η R : ℝ} (he : 0<η) (he1 : η<1) (hR : 0<R) :
    ∃ T : ℕ, ∀ t ≥ T, let m := crossingCount (2*t) t
    let A := firstQuarterRanks (lowerRank t) m
    let B := lastQuarterRanks (lowerRank t) m
    8 ≤ m →
    ((m:ℝ)/8 ≤ A.card ∧ (m:ℝ)/8 ≤ B.card) ∧
    (∀ i ∈ A ∪ B, 0 < normalizedA t i ∧ (m:ℝ)/(2*t) ≤ normalizedB t i-normalizedA t i ∧
      normalizedA t i ∈ Ioo (1-R) (1+R) ∧ normalizedB t i ∈ Ioo (1-R) (1+R)) ∧
    (∀ i ∈ A, ∀ j ∈ B, (m:ℝ)/(4*t) ≤ normalizedA t i-normalizedA t j ∧
      (m:ℝ)/(4*t) ≤ normalizedB t i-normalizedB t j) ∧
    (∀ z ∈ Icc 0 (Real.log (7/6)), let X := scaleX η t z
      let Q := scaleQ η t z
      let N := ⌊X/Q⌋₊
      ∀ i ∈ A ∪ B, (X/t)*normalizedA t i ∈ Icc Q (2*Q) ∧
        (X/t)*normalizedB t i ∈ Icc Q (2*Q) ∧
        i ∈ Finset.range (min (signSet true N).card (signSet false N).card) ∧
        ∀ s : Bool, indexAt (signSet s N) i = indexAt (signSet s (2*t)) i) := by
  let δ := min (R/4) (1/8)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hd8 : δ ≤ 1/8 := min_le_right _ _
  have hdR : δ ≤ R/4 := min_le_left _ _
  obtain ⟨T,hg⟩ := localized_groups hδ
  refine ⟨max T 4,?_⟩
  intro t ht
  dsimp only
  intro hm8
  let m := crossingCount (2*t) t
  let A := firstQuarterRanks (lowerRank t) m
  let B := lastQuarterRanks (lowerRank t) m
  have ht4 : 4 ≤ t := (le_max_right T 4).trans ht
  have ht0 : (0:ℝ) < t := Nat.cast_pos.mpr (by omega)
  have hT := (le_max_left T 4).trans ht
  obtain ⟨hA,hB,hgen,hrow,hsep⟩ := hg t hT (2*t) (by omega) hm8
  have near {i : ℕ} (hi : i ∈ A ∪ B) :
      |(lowerEndpoint t i:ℝ)-t| ≤ δ*t ∧ |(upperEndpoint t i:ℝ)-t| ≤ δ*t := by
    have h₁ := (hgen i hi true).2.2
    have h₂ := (hgen i hi false).2.2
    unfold lowerEndpoint upperEndpoint
    by_cases e : indexAt (signSet true (2*t)) i ≤ indexAt (signSet false (2*t)) i
    · simpa [min_eq_left e,max_eq_right e] using And.intro h₁ h₂
    · have e' := le_of_not_ge e
      simpa [min_eq_right e',max_eq_left e'] using And.intro h₂ h₁
  have localData {x : ℕ} (hx : |(x:ℝ)-t| ≤ δ*t) :
      0 < (x:ℝ) ∧ (x:ℝ) ∈ Icc (7*(t:ℝ)/8) (9*(t:ℝ)/8) ∧ (t:ℝ)/x ∈ Ioo (1-R) (1+R) := by
    have hd := normalized_endpoint_near_one ht0 hδ.le (by linarith) hx
    have h := abs_le.mp hx
    have h' := abs_le.mp hd.2
    have h8 := mul_le_mul_of_nonneg_right hd8 ht0.le
    exact ⟨hd.1,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  refine ⟨⟨hA,hB⟩,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hp,hq⟩ := near hi
    have P := localData hp
    have Q := localData hq
    have he := hrow i hi
    have gap : lowerEndpoint t i + m ≤ upperEndpoint t i := by
      unfold lowerEndpoint upperEndpoint
      dsimp only at he
      omega
    have gr : (m:ℝ) ≤ (upperEndpoint t i:ℝ)-lowerEndpoint t i := by
      have hh : (lowerEndpoint t i:ℝ)+m ≤ upperEndpoint t i := by exact_mod_cast gap
      linarith
    exact ⟨div_pos ht0 Q.1,normalized_reciprocal_gap ht0 P.1 Q.1 P.2.1.2 Q.2.1.2 (Nat.cast_nonneg _) gr,
      Q.2.2,P.2.2⟩
  · intro i hi j hj
    have hi' : i ∈ A ∪ B := Finset.mem_union_left _ hi
    have hj' : j ∈ A ∪ B := Finset.mem_union_right _ hj
    have h₁ := hsep i hi j hj true
    have h₂ := hsep i hi j hj false
    have hs : m ≤ 2*(upperEndpoint t j - upperEndpoint t i) ∧
        m ≤ 2*(lowerEndpoint t j-lowerEndpoint t i) := by
      unfold upperEndpoint lowerEndpoint
      change m ≤ _ at h₁ h₂
      have h8 : 8 ≤ m := hm8
      omega
    have recGap {x y : ℕ} (h : m ≤ 2*(y-x))
        (hx : |(x:ℝ)-t|≤δ*t) (hy : |(y:ℝ)-t|≤δ*t) :
        (m:ℝ)/(4*t) ≤ (t:ℝ)/x-t/y := by
      have hxy : x ≤ y := by have h8 : 8 ≤ m := hm8; omega
      have hreal : (m:ℝ) ≤ 2*((y-x:ℕ):ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub hxy] at hreal
      have eg := normalized_reciprocal_gap ht0 (localData hx).1 (localData hy).1
        (localData hx).2.1.2 (localData hy).2.1.2 (m := (m:ℝ)/2) (by positivity) (by linarith)
      refine le_trans (le_of_eq ?_) eg
      ring
    exact ⟨recGap hs.1 (near hi').2 (near hj').2,recGap hs.2 (near hi').1 (near hj').1⟩
  · intro z hz i hi
    let X := scaleX η t z
    let Q := scaleQ η t z
    let N := ⌊X/Q⌋₊
    obtain ⟨hN,hratio⟩ := scaleN_window he he1 ht4 hz.1 hz.2
    have hX : 0<X := by unfold X scaleX nominalX; positivity
    have hQ : 0<Q := by unfold Q scaleQ; exact Real.rpow_pos_of_pos hX _
    have hL : X/t ∈ Icc (3*Q/2) (7*Q/4) := by
      change X/Q ∈ Set.Icc _ _ at hratio
      have e₁ := (le_div_iff₀ hQ).mp hratio.1
      have e₂ := (div_le_iff₀ hQ).mp hratio.2
      exact ⟨(le_div_iff₀ ht0).2 (by linarith),(div_le_iff₀ ht0).2 (by linarith)⟩
    have live := (hg t hT N hN hm8).2.2.1 i hi
    exact ⟨normalized_endpoint_in_shell hQ ht0 hL (localData (near hi).2).2.1,
      normalized_endpoint_in_shell hQ ht0 hL (localData (near hi).1).2.1,
      Finset.mem_range.mpr (lt_min (live true).1 (live false).1),fun s => (live s).2.1⟩

end RHConnections.RankContrast
