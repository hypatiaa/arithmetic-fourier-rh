import AstraSharpRadialTail
import AstraRampVariation

open MeasureTheory Set Filter
open scoped ContDiff
noncomputable section
namespace RHConnections.SharpRadialTail
open SpectralTail SmoothedPrimeLimit SmoothedPrimeSandwichUniform PrimeRightCut

theorem sharpened_zero_remainder :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {a b h T : ℝ} (J : ℕ), a ≤ b → 0 < h →
    0 < a → b+h < 3 → 0 ≤ T → (2:ℝ)^J ≤ Real.exp (T/3) → Real.exp (T/3) ≤ (2:ℝ)^(J+1) →
    let f := fun x : ℝ => (shell a b h x : ℂ)
    ‖(∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r) - rightSum T f‖ ≤
      A*Real.exp (-(T/6))*((J:ℝ)+2)^2 + (B/h)*((J:ℝ)+1)/(2:ℝ)^J := by
  classical
  obtain ⟨A,hA,hlo⟩ := low_inverse_first
  obtain ⟨B,hB,hhi⟩ := high_inverse_square
  let K := Real.exp 3*(2*curvatureMass)
  let L := Real.exp 3*2
  have hK : 0 ≤ K := by dsimp [K,curvatureMass]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L*A,K*B,mul_nonneg hL hA,mul_nonneg hK hB,?_⟩
  intro a b h T J hab hh ha hb hT hJ hJ'
  let f := fun x : ℝ => (shell a b h x : ℂ)
  let F := fun r : NontrivialZetaZero => compactZeroTerm (scaleTest T f) r
  let G := (rightSet T).indicator F
  let E := Real.exp (-(T/6))
  let S : Set NontrivialZetaZero := {r | ‖r.val‖ ≤ (2:ℝ)^(J+1)}
  let U : Set NontrivialZetaZero := {r | (2:ℝ)^J ≤ ‖r.val‖}
  let v (r : NontrivialZetaZero) := mass r/‖r.val‖
  let v₂ (r : NontrivialZetaZero) := mass r/‖r.val‖^2
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hn (r : NontrivialZetaZero) : 0 < ‖r.val‖ := by
    obtain ⟨δ,hd,hr⟩ := zeta_zero_norm_lower
    exact hd.trans_le (hr r)
  have hvn (r : NontrivialZetaZero) : 0 ≤ S.indicator v r := Set.indicator_nonneg
    (fun r _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) _
  have hwN (r : NontrivialZetaZero) : 0 ≤ U.indicator v₂ r := Set.indicator_nonneg
    (fun r _ => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) _
  have hsV : Summable (S.indicator v) := by
    apply (zeta_inverse_square_with_multiplicity.mul_right ((2:ℝ)^(J+1))).of_nonneg_of_le hvn
    intro r
    by_cases e : r ∈ S
    · rw [indicator_of_mem e]
      change mass r/‖r.val‖ ≤ (mass r/‖r.val‖^2)*((2:ℝ)^(J+1))
      calc
        _ = (mass r/‖r.val‖^2)*‖r.val‖ := by have hne := (hn r).ne'; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left e (by dsimp [mass]; positivity)
    · rw [indicator_of_notMem e]; positivity
  have hsW : Summable (U.indicator v₂) := zeta_inverse_square_with_multiplicity.indicator _
  have hvS : (∑' r, S.indicator v r) ≤ A*((J:ℝ)+2)^2 := by
    rw [← _root_.tsum_subtype]
    rw [show (J:ℝ)+2 = ((J+1:ℕ):ℝ)+1 by push_cast; ring]
    exact hlo (J+1)
  have hwS : (∑' r, U.indicator v₂ r) ≤ B*((J:ℝ)+1)/(2:ℝ)^J := by
    rw [← _root_.tsum_subtype]
    exact hhi J
  have hz (x : ℝ) (hx : x ≤ 0) : f x = 0 := by simp [f,shell_left hab hh (hx.trans ha.le)]
  have hfac (r : NontrivialZetaZero) :
      ‖F r‖ = Real.exp ((r.val.re-1)*T) * ‖compactZeroTerm (scaleTest 0 f) r‖ := by
    simp only [F,scaled_zero_term_eq hz hT,norm_mul,Complex.norm_exp,Complex.mul_re,
      Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hfull (r : NontrivialZetaZero) : ‖F r‖ ≤ (K/h)*v₂ r := by
    rw [hfac]
    apply (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr r.property.1.2.le) hT))).trans
    exact (spectral_majorant hab hh ha hb r).trans_eq (mul_comm _ _)
  have hsF : Summable F := Summable.of_norm <|
    (zeta_inverse_square_with_multiplicity.mul_left (K/h)).of_nonneg_of_le (fun _ => norm_nonneg _) hfull
  have hsG : Summable G := hsF.indicator _
  have hsplit (r : NontrivialZetaZero) : ‖F r-G r‖ ≤
      (L*E)*(S.indicator v r) + (K/h)*(U.indicator v₂ r) := by
    have hLn := mul_nonneg (mul_nonneg hL hE) (hvn r)
    have hRn := mul_nonneg (div_nonneg hK hh.le) (hwN r)
    by_cases e : r ∈ rightSet T
    · simp only [G,indicator_of_mem e,sub_self,norm_zero]
      exact add_nonneg hLn hRn
    rw [show G r=0 from indicator_of_notMem e _,sub_zero]
    by_cases H : ‖r.val‖ ≤ Real.exp (T/3)
    · have hβ : r.val.re ≤ 5/6 := le_of_not_gt fun i => e ⟨i,H⟩
      apply le_add_of_le_of_nonneg _ hRn
      rw [hfac,indicator_of_mem (show r ∈ S from H.trans hJ')]
      have he : Real.exp ((r.val.re-1)*T) ≤ E := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hβ hT])
      exact (mul_le_mul he (spectral_first_majorant hab hh ha hb r) (norm_nonneg _) hE).trans_eq (by dsimp only [L,v,mass]; ring)
    · apply le_add_of_nonneg_of_le hLn
      rw [indicator_of_mem (show r ∈ U from hJ.trans (le_of_not_ge H))]
      exact hfull r
  have hsm := (hsV.mul_left (L*E)).add (hsW.mul_left (K/h))
  have hs := hsm.of_nonneg_of_le (fun r => norm_nonneg (F r-G r)) hsplit
  change ‖(∑' r, F r)-(∑' r,G r)‖ ≤ _
  rw [← hsF.tsum_sub hsG]
  calc
    _ ≤ ∑' r, ‖F r-G r‖ := norm_tsum_le_tsum_norm hs
    _ ≤ _ := (hs.tsum_le_tsum hsplit hsm).trans <| by
      rw [((hsV.mul_left (L*E)).tsum_add (hsW.mul_left (K/h))),tsum_mul_left,tsum_mul_left]
      exact (add_le_add (mul_le_mul_of_nonneg_left hvS (mul_nonneg hL hE))
        (mul_le_mul_of_nonneg_left hwS (div_nonneg hK hh.le))).trans_eq (by dsimp only [E]; ring)

#print axioms sharpened_zero_remainder
end RHConnections.SharpRadialTail
