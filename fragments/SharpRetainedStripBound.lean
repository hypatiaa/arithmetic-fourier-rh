import Verified

open Set Filter
noncomputable section
namespace RHConnections.SharpRightEndpoint
open SpectralTail SmoothedPrimeLimit SmoothedPrimeSandwichUniform PrimeRightCut SharpRadialTail

theorem retained_bound_of_strip {a : ℝ} (hStrip : ∀ s : ℂ, a<s.re → riemannZeta s≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T≥1, retained T ≤ C*Real.exp ((a-1)*T)*(T+2)^2 := by
  classical
  obtain ⟨A,hA,hlo⟩ := low_inverse_first
  let L := Real.exp 3*2
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨L*A,mul_nonneg hL hA,?_⟩
  intro T hT
  have ht0 : 0≤T := by linarith
  have he : 1≤Real.exp (T/3) := Real.one_le_exp (by linarith)
  obtain ⟨J,hl,hr⟩ := exists_nat_pow_near he (by norm_num : (1:ℝ)<2)
  have hlog : (1/2:ℝ) ≤ Real.log 2 := by
    have e := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at e
    norm_num at e
    linarith
  have hlogJ := Real.log_le_log (by positivity : (0:ℝ)<2^J) hl
  rw [Real.log_pow,Real.log_exp] at hlogJ
  have hJ : (J:ℝ) ≤ T := by nlinarith [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α:=ℝ) J)]
  let S : Set NontrivialZetaZero := {r | ‖r.val‖ ≤ (2:ℝ)^(J+1)}
  let v (r : NontrivialZetaZero) := SharpRadialTail.mass r/‖r.val‖
  have hvn (r : NontrivialZetaZero) : 0 ≤ S.indicator v r :=
    Set.indicator_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) _
  have hsV : Summable (S.indicator v) := by
    apply (zeta_inverse_square_with_multiplicity.mul_right ((2:ℝ)^(J+1))).of_nonneg_of_le hvn
    intro r
    by_cases e : r ∈ S
    · rw [indicator_of_mem e]
      change SharpRadialTail.mass r/‖r.val‖ ≤ (SharpRadialTail.mass r/‖r.val‖^2)*((2:ℝ)^(J+1))
      calc
        _ = (SharpRadialTail.mass r/‖r.val‖^2)*‖r.val‖ := by
          obtain ⟨δ,hd,h⟩ := zeta_zero_norm_lower
          have hn := (hd.trans_le (h r)).ne'
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left e (by dsimp [SharpRadialTail.mass]; positivity)
    · rw [indicator_of_notMem e]; positivity
  have hvS : (∑' r, S.indicator v r) ≤ A*((J:ℝ)+2)^2 := by
    rw [← _root_.tsum_subtype]
    rw [show (J:ℝ)+2 = ((J+1:ℕ):ℝ)+1 by push_cast; ring]
    exact hlo (J+1)
  let E := Real.exp ((a-1)*T)
  have hE : 0≤E := (Real.exp_pos _).le
  let ids := (rightSet_finite T).toFinset
  have hsum := (hsV.sum_le_tsum ids (fun r _ => hvn r)).trans hvS
  have hJs : ((J:ℝ)+2)^2≤(T+2)^2 := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hshell {u b h : ℝ} (hub : u≤b) (hh : 0<h) (hu : 0<u) (hb : b+h<3) :
      ‖shellRight T u b h‖ ≤ L*A*E*(T+2)^2 := by
    let f := fun x : ℝ => (shell u b h x : ℂ)
    have hz (x : ℝ) (hx : x≤0) : f x=0 := by simp [f,shell_left hub hh (hx.trans hu.le)]
    change ‖rightSum T f‖ ≤ _
    rw [rightSum_finite]
    calc
      _ ≤ ∑ r∈ids, ‖compactZeroTerm (scaleTest T f) r‖ := norm_sum_le _ _
      _ ≤ ∑ r∈ids, (L*E)*S.indicator v r := by
        apply Finset.sum_le_sum
        intro r hr'
        have hrmem : r∈rightSet T := by simpa [ids] using hr'
        have hrS : r∈S := hrmem.2.trans hr.le
        rw [indicator_of_mem hrS,scaled_zero_term_eq hz ht0,norm_mul,Complex.norm_exp]
        have hβ : r.val.re ≤ a := le_of_not_gt (fun h => hStrip _ h r.property.2)
        have hex : Real.exp ((r.val.re-1)*T)≤E := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (sub_le_sub_right hβ 1) ht0)
        simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,
          mul_zero,sub_zero]
        exact (mul_le_mul hex (spectral_first_majorant hub hh hu hb r) (norm_nonneg _) hE).trans_eq
          (by dsimp only [v,L,SharpRadialTail.mass]; ring)
      _ = (L*E)*∑ r∈ids,S.indicator v r := (Finset.mul_sum ..).symm
      _ ≤ (L*E)*(A*(T+2)^2) := mul_le_mul_of_nonneg_left
        (hsum.trans (mul_le_mul_of_nonneg_left hJs hA)) (mul_nonneg hL hE)
      _ = _ := by ring
  have hw : 0<width T := by dsimp [width]; positivity
  have hw1 : width T≤1/8 := by
    have h := Real.exp_le_one_iff.mpr (show -(T/6)≤0 by linarith)
    dsimp [width]
    linarith
  have hlog' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  exact max_le (hshell (by linarith) hw (by norm_num) (by linarith))
    (hshell (by linarith) hw (by linarith) (by linarith))
end RHConnections.SharpRightEndpoint
