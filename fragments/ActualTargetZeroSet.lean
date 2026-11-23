import Verified

noncomputable section
open Set
namespace RHConnections.LongRankPhase
open PhaseWindow RHConnections.RankContrast RHConnections.LocalModeContrast

abbrev OtherRightZero (target : RightZero) := {r : RightZero // r≠target}

def otherRightValue (target : RightZero) (r : OtherRightZero target) : ℂ := rightValue r.val

theorem right_value_injective : Function.Injective rightValue := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem shifted_other_count (h : ZetaDensityPremise) (target : RightZero) :
    ∃ C : ℝ, 0≤C ∧ ∀ (T : ℝ) (s : Finset (OtherRightZero target)), 1≤T →
      (∀ r∈s, |(otherRightValue target r-rightValue target).im|≤T) →
      (s.card:ℝ)≤C*Real.sqrt T := by
  obtain ⟨C,hC,hCount⟩ := shifted_right_zero_sqrt_count h (rightValue target)
  refine ⟨C,hC,?_⟩
  intro T s hT hs
  let e : OtherRightZero target ↪ RightZero := ⟨Subtype.val,Subtype.val_injective⟩
  have hh := hCount T (s.map e) hT (by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hr
    exact hs x hx)
  rwa [Finset.card_map] at hh

theorem shifted_other_near_finite (target : RightZero) :
    {r : OtherRightZero target | |(otherRightValue target r-rightValue target).im|<2}.Finite := by
  let T := 2+|(rightValue target).im|
  have h := finite_right_zeros_of_bounded_height T
  apply (h.preimage (Set.injOn_of_injective Subtype.val_injective)).subset
  intro r hr
  have hTri := abs_add_le ((rightValue r.val).im-(rightValue target).im) (rightValue target).im
  rw [sub_add_cancel] at hTri
  have hh : |(rightValue r.val).im-(rightValue target).im|<2 := by
    change |(otherRightValue target r-rightValue target).im|<2 at hr
    simpa only [Complex.sub_im,otherRightValue] using hr
  have hl : |(rightValue r.val).im|≤T := by dsimp [T]; linarith only [hTri,hh]
  exact hl

def otherHeightFinset (target : RightZero) (T : ℝ) : Finset (OtherRightZero target) := by
  classical
  exact (rightHeightFinset T).subtype (·≠target)

theorem right_potential_target_split (target : RightZero) (Q : ℝ)
    (ht : |(rightValue target).im|<Q^(1/8:ℝ)) (x : ℝ) :
    rightPotential Q x =
      (zeroMultiplicity target:ℂ)*zeroPrimitive (rightValue target) x+
        ∑ r∈otherHeightFinset target (Q^(1/8:ℝ)),
          (zeroMultiplicity r.val:ℂ)*zeroPrimitive (otherRightValue target r) x := by
  classical
  let s := rightHeightFinset (Q^(1/8:ℝ))
  let f (r : RightZero) := (zeroMultiplicity r:ℂ)*zeroPrimitive (rightValue r) x
  have hm : target∈s := (right_height_finite _).mem_toFinset.mpr ht
  have heq : (s.subtype (·≠target)).map ⟨Subtype.val,Subtype.val_injective⟩ = s.erase target := by
    ext r
    constructor
    · intro hr
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hr
      exact Finset.mem_erase.mpr ⟨y.property,Finset.mem_subtype.mp hy⟩
    · intro hr
      obtain ⟨hn,hs⟩ := Finset.mem_erase.mp hr
      exact Finset.mem_map.mpr ⟨⟨r,hn⟩,Finset.mem_subtype.mpr hs,rfl⟩
  change (∑ r∈s,f r)=f target+∑ r∈s.subtype (·≠target),f r.val
  have hh := Finset.sum_erase_add (f := f) s hm
  rw [←heq,Finset.sum_map] at hh
  exact hh.symm.trans (add_comm _ _)

end RHConnections.LongRankPhase
