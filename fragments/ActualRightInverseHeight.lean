import Verified
import ActualWeightedRightDensity
import PhaseDensityTransfer

noncomputable section
open Set
namespace RHConnections.PhaseWindow
open SpectralTail ZetaDiskLog PrimeErrorLaplace PoleCompensation

abbrev RightOccurrence := Σ r : RightZero, Fin (rightMultiplicity r)

theorem right_zero_nonzero_ordinate (r : RightZero) : (rightValue r).im≠0 := by
  intro him
  have hz : rightValue r=((rightValue r).re:ℂ) := by
    apply Complex.ext <;> simp [him]
  have hp : 0<(rightValue r).re := r.val.property.1.1
  have h1 : rightValue r≠1 := by
    intro h
    have hh : (rightValue r).re<1 := r.val.property.1.2
    rw [h] at hh
    norm_num at hh
  have hn := regularized_zeta_ne_zero_positive_real hp
  have h := (regularizedZeta_germ h1).eq_of_nhds
  have hr : riemannZeta (rightValue r)=0 := r.val.property.2
  rw [hr,mul_zero,hz] at h
  exact hn h

theorem right_finite_of_bounded_weighted_inverse_heights (hIngham : ZetaDensityPremise) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : Finset RightZero,
      (∑ r∈s,(rightMultiplicity r:ℝ)/ |(rightValue r).im|)≤C := by
  classical
  obtain ⟨C,hC,hCount⟩ := hIngham
  let T₁ : Set RightZero := {r | |(rightValue r).im|≤2}
  have hT₁ : T₁.Finite := finite_right_zeros_of_bounded_height 2
  let val (r : RightOccurrence) := rightValue r.1
  have hFinite : {r : RightOccurrence | |(val r).im|<2}.Finite := by
    let s := hT₁.toFinset.sigma (fun r => (Finset.univ : Finset (Fin (rightMultiplicity r))))
    apply s.finite_toSet.subset
    intro r hr
    apply Finset.mem_sigma.mpr
    exact ⟨hT₁.mem_toFinset.mpr (show |(rightValue r.1).im|≤2 from (show |(val r).im|<2 from hr).le),
      Finset.mem_univ _⟩
  let A := C*(120*6^5)*Real.sqrt 2
  have hA : 0≤A := by dsimp [A]; positivity
  have hDensity (T : ℝ) (s : Finset RightOccurrence) (hT : 1≤T)
      (hHeight : ∀ r∈s, |(val r).im|≤T) : (s.card:ℝ)≤A*Real.sqrt T := by
    let P := s.image Sigma.fst
    let hull := P.sigma (fun r => (Finset.univ : Finset (Fin (rightMultiplicity r))))
    have hsub : s⊆hull := by
      intro r hr
      exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ hr,Finset.mem_univ _⟩
    have hc : (s.card:ℝ)≤∑ r∈P,(rightMultiplicity r:ℝ) := by
      have hh : (s.card:ℝ)≤hull.card := Nat.cast_le.mpr (Finset.card_le_card hsub)
      rw [show hull=P.sigma (fun _ => Finset.univ) from rfl,Finset.card_sigma,Nat.cast_sum] at hh
      simpa only [Finset.card_univ,Fintype.card_fin] using hh
    let e : RightZero ↪ NontrivialZetaZero := ⟨Subtype.val,Subtype.val_injective⟩
    have hh := hCount (2*T) (1/8) (P.map e) (by linarith) (by norm_num) (by norm_num) (by
      intro r hr
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hr
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hx
      subst x
      exact ⟨by change 1-(1/8:ℝ)≤w.1.val.val.re; linarith [w.1.property],
        (hHeight w hw).trans (by linarith)⟩)
    simp only [Finset.sum_map,e,Function.Embedding.coeFn_mk] at hh
    rw [show (3*(1/8:ℝ)/(1+1/8))=1/3 by norm_num] at hh
    calc
      _ ≤ _ := hc.trans hh
      _ = C*((2*T)^(1/3:ℝ)*(Real.log (2*T))^5) := by ring
      _ ≤ C*((120*6^5)*Real.sqrt (2*T)) :=
        mul_le_mul_of_nonneg_left (log_fifth_third_le_sqrt (by linarith)) hC
      _ = _ := by dsimp [A]; rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]; ring
  have hsum := opposite_offsets_summable_of_sqrt_count val hFinite A hA hDensity
  let z (r : RightOccurrence) := |(val r).im|⁻¹
  have hz : Summable z := by
    have hh := hsum.mul_left Real.pi⁻¹
    have he : (fun r : RightOccurrence => Real.pi⁻¹*oppositeOffset (val r))=z := by
      ext r
      unfold oppositeOffset z
      rw [div_eq_mul_inv,←mul_assoc,inv_mul_cancel₀ Real.pi_ne_zero,one_mul]
    rwa [he] at hh
  refine ⟨∑' r,z r,tsum_nonneg (by intro r; dsimp [z]; positivity),?_⟩
  intro s
  let pool : Finset RightOccurrence := s.sigma (fun r => Finset.univ)
  have hpool := hz.sum_le_tsum pool (fun r _ => by dsimp [z]; positivity)
  rw [show pool=s.sigma (fun _ => Finset.univ) from rfl,Finset.sum_sigma] at hpool
  convert hpool using 1
  apply Finset.sum_congr rfl
  intro r _
  simp [z,val,nsmul_eq_mul,div_eq_mul_inv]

end RHConnections.PhaseWindow
