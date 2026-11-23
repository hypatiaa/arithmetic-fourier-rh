import Verified
import MobiusRankLocalization
import RankNormalizedGeometry

noncomputable section
namespace RHConnections.MobiusRankLocalization
open RankPairing MobiusCrossingLengths

def lowerRank (t : ℕ) := min (signSet true t).card (signSet false t).card

theorem localized_groups {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ t ≥ T, ∀ N : ℕ, 5*t ≤ 4*N →
    let q := lowerRank t
    let m := crossingCount (2*t) t
    8 ≤ m →
    ((m:ℝ)/8 ≤ (firstQuarterRanks q m).card) ∧
    ((m:ℝ)/8 ≤ (lastQuarterRanks q m).card) ∧
    (∀ i ∈ firstQuarterRanks q m ∪ lastQuarterRanks q m, ∀ s : Bool,
      i < (signSet s N).card ∧
      indexAt (signSet s N) i = indexAt (signSet s (2*t)) i ∧
      |(indexAt (signSet s N) i:ℝ)-t| ≤ δ*t) ∧
    (∀ i ∈ firstQuarterRanks q m ∪ lastQuarterRanks q m,
      let x := indexAt (signSet true N) i
      let y := indexAt (signSet false N) i
      (x ≤ t ∧ t < y ∧ x+m ≤ y) ∨ (y ≤ t ∧ t < x ∧ y+m ≤ x)) ∧
    (∀ i ∈ firstQuarterRanks q m, ∀ j ∈ lastQuarterRanks q m, ∀ s : Bool,
      m ≤ 2*(indexAt (signSet s N) j-indexAt (signSet s N) i)) := by
  obtain ⟨T,hT⟩ := uniform_interior hδ
  refine ⟨T,?_⟩
  intro t ht N hN
  let p := (signSet true t).card
  let n := (signSet false t).card
  let q := lowerRank t
  let m := crossingCount (2*t) t
  have hq : q = min p n := rfl
  have hm : m = max p n - min p n := by
    unfold m crossingCount
    change max (prefixCount (signSet true (2*t)) t) (prefixCount (signSet false (2*t)) t) -
      min (prefixCount (signSet true (2*t)) t) (prefixCount (signSet false (2*t)) t) = _
    rw [prefix_stable true (by omega),prefix_stable false (by omega)]
  dsimp only
  intro hm8
  have hr {i} (hi : i ∈ firstQuarterRanks q m ∪ lastQuarterRanks q m) :
      min p n ≤ i ∧ i < max p n := by
    simp only [Finset.mem_union,firstQuarterRanks,lastQuarterRanks,Finset.mem_Ico] at hi
    omega
  have hgen {i} (hi : i ∈ firstQuarterRanks q m ∪ lastQuarterRanks q m) (s : Bool) :
      i < (signSet s N).card ∧ indexAt (signSet s N) i = indexAt (signSet s (2*t)) i ∧
      |(indexAt (signSet s N) i:ℝ)-t| ≤ δ*t := by
    obtain ⟨hl,hu⟩ := hr hi
    obtain ⟨hg,hd⟩ := hT t ht N hN i hl hu s
    have hg' := (hT t ht (2*t) (by omega) i hl hu s).1
    refine ⟨hg,?_,by simpa [paddedAt,hg] using hd⟩
    by_cases hn : N ≤ 2*t
    · exact (index_stable hn s hg).symm
    · exact index_stable (le_of_not_ge hn) s hg'
  have pc (s : Bool) := prefix_stable s (N := N) (n := t) (by omega)
  have bounds {s b : Bool} {i : ℕ} (hl : (signSet b t).card ≤ i) (hu : i < (signSet s t).card)
      (hb : i < (signSet b N).card) (hs : i < (signSet s N).card) :
      indexAt (signSet s N) i ≤ t ∧ t < indexAt (signSet b N) i ∧
      indexAt (signSet s N) i + ((signSet s t).card - (signSet b t).card) ≤ indexAt (signSet b N) i := by
    have h₁ : prefixCount (signSet b N) t ≤ i := (pc b).trans_le hl
    have h₂ : i < prefixCount (signSet s N) t := hu.trans_eq (pc s).symm
    have h₃ := (crossing_iff (A := signSet s N) (B := signSet b N) (N := N) (by omega : t ≤ N)).2 ⟨h₁,h₂⟩
    have h₄ := genuine_length (N := N) h₁ h₂ hb
    simp only [paddedAt,ite_eq_left hs,ite_eq_left hb] at h₃ h₄
    rw [pc,pc] at h₄
    exact ⟨h₃.1,h₃.2,by omega⟩
  obtain ⟨hF,hL⟩ := first_last_quarter_sizes (q := q) (show 8 ≤ m from hm8)
  refine ⟨hF,hL,fun i hi s => hgen hi s,?_,?_⟩
  · intro i hi
    obtain ⟨hl,hu⟩ := hr hi
    by_cases h : n ≤ p
    · left
      have hm' : crossingCount (2*t) t = p-n := by change m = _; omega
      simpa only [hm'] using bounds (s := true) (b := false) (by change n ≤ i; omega)
        (by change i < p; omega) (hgen hi false).1 (hgen hi true).1
    · right
      have hm' : crossingCount (2*t) t = n-p := by change m = _; omega
      simpa only [hm'] using bounds (s := false) (b := true) (by change p ≤ i; omega)
        (by change i < n; omega) (hgen hi true).1 (hgen hi false).1
  · intro i hi j hj s
    have hg := (hgen (Finset.mem_union_right _ hj) s).1
    change i ∈ Finset.Ico q (q+m/4) at hi
    change j ∈ Finset.Ico (q+m-m/4) (q+m) at hj
    obtain ⟨hi1,hi2⟩ := Finset.mem_Ico.mp hi
    obtain ⟨hj1,hj2⟩ := Finset.mem_Ico.mp hj
    have hd := index_gap (S := signSet s N) (i := i) (j := j) (by omega) hg
    omega

end RHConnections.MobiusRankLocalization
