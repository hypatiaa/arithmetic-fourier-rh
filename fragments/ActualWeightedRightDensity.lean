import Verified
import WeightedRightDensity
import ZetaRightDensity

noncomputable section
namespace RHConnections.PhaseWindow
open SpectralTail

def rightMultiplicity (r : RightZero) : ℕ := analyticOrderNatAt riemannZeta (rightValue r)

theorem weighted_right_finset (hIngham : ZetaDensityPremise) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Finset RightZero) (Q T : ℝ),
      1<Q → 2≤T → T≤Q^(1/6:ℝ) → (∀ r∈s, |(rightValue r).im|≤T) →
      (∑ r∈s,(rightMultiplicity r:ℝ)*Q^((rightValue r).re-1))≤C*(Real.log T)^5 := by
  classical
  obtain ⟨A,hA,hc⟩ := hIngham
  let den := (1-Real.exp (-(1/2)))⁻¹
  have hd : 0≤den := inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))
  refine ⟨A*Real.exp (1/2)*den,by positivity,?_⟩
  intro s Q T hQ hT hTQ ht
  let pool : Finset (Σ r : RightZero, Fin (rightMultiplicity r)) :=
    s.sigma (fun _ => Finset.univ)
  let beta (r : Σ r : RightZero, Fin (rightMultiplicity r)) := (rightValue r.1).re
  have hBeta (r) (hr : r∈pool) : 1/2≤beta r ∧ beta r≤1 :=
    ⟨by change (1/2:ℝ)≤r.1.val.val.re; linarith [r.1.property],(r.1.val.property.1.2).le⟩
  have hCard (u : ℝ) (hu : 0≤u) (hu1 : u≤1/2) :
      ((pool.filter (fun r => 1-u≤beta r)).card:ℝ) ≤
        A*(Real.log T)^5*T^(3*u/(1+u)) := by
    let P := s.filter (fun r => 1-u≤(rightValue r).re)
    have hEq : pool.filter (fun r => 1-u≤beta r) =
        P.sigma (fun _ => Finset.univ) := by
      ext r
      simp [P,pool,beta]
    rw [hEq,Finset.card_sigma,Nat.cast_sum]
    simp only [Finset.card_univ,Fintype.card_fin]
    let e : RightZero ↪ NontrivialZetaZero := ⟨Subtype.val,Subtype.val_injective⟩
    have hh := hc T u (P.map e) hT hu hu1 (by
      intro r hr
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hr
      obtain ⟨hx₁,hx₂⟩ := Finset.mem_filter.mp hx
      exact ⟨hx₂,ht x hx₁⟩)
    simp only [Finset.sum_map,e,Function.Embedding.coeFn_mk] at hh
    exact hh.trans_eq (by ring)
  have hBound := weighted_rank_density_bound pool beta hQ (by linarith : 1≤T) hTQ hA hBeta hCard
  have hSum : (∑ i∈pool,Q^(beta i-1)) =
      ∑ r∈s,(rightMultiplicity r:ℝ)*Q^((rightValue r).re-1) := by
    rw [show pool=s.sigma (fun _ => Finset.univ) from rfl,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    simp [beta,nsmul_eq_mul]
  rw [hSum] at hBound
  exact hBound.trans_eq (by dsimp [den]; ring)

end RHConnections.PhaseWindow
