import Verified

open Metric
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter SpectralTail HurwitzTailGrowth

theorem completed_dirichlet_envelope {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : MellinGrowthEnvelope (completedLFunction χ) := by
  have hn : N ≠ 1 := hχ ∘ level_one' _
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hc (s : ℂ) : completedLFunction χ s = ZMod.completedLFunction₀ χ s := by
    rw [completedLFunction, ZMod.completedLFunction_eq, χ.map_zero' hn,
      χ.sum_eq_zero_of_ne_one hχ]
    simp
  rw [show completedLFunction χ = ZMod.completedLFunction₀ χ from funext hc]
  unfold ZMod.completedLFunction₀
  have hN := MellinGrowthEnvelope.nat_cpow_neg hpos
  have hE := MellinGrowthEnvelope.finset_sum (Finset.univ : Finset (ZMod N))
    (fun j s => χ j * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s)
    (fun j _ => (completed_hurwitz_even_envelope (ZMod.toAddCircle j)).const_mul _)
  have hO := MellinGrowthEnvelope.finset_sum (Finset.univ : Finset (ZMod N))
    (fun j s => χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
    (fun j _ => (completed_hurwitz_odd_envelope (ZMod.toAddCircle j)).const_mul _)
  exact (hN.mul hE).add (hN.mul hO)

theorem jensen_growth_of_envelope {f : ℂ → ℂ} (hg : MellinGrowthEnvelope f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Metric.sphere (2:ℂ) R,
      Real.log ‖f s‖ ≤ A*(R+2)*Real.log (R+2) := by
  obtain ⟨C,D,hC,hD,hg⟩ := hg
  let C₁ := max C 1
  have h1 : 1 ≤ C₁ := le_max_right _ _
  have h₁ : 0 < C₁ := zero_lt_one.trans_le h1
  let E := Real.log C₁/Real.log 2
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hE : 0 ≤ E := div_nonneg (Real.log_nonneg h1) hlog.le
  refine ⟨D+E,add_nonneg hD hE,?_⟩
  intro R hR s hs
  let u := R+2
  have hu : 2 ≤ u := by dsimp [u]; linarith
  have hu0 : 0 ≤ u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hn : ‖s‖ ≤ u := by
    have hs' : ‖s-(2:ℂ)‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hs
    calc
      _ = ‖s-2+2‖ := by rw [sub_add_cancel]
      _ ≤ ‖s-2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [hs', Complex.norm_two]
  have hCf : ‖f s‖ ≤ C₁*Real.exp (D*u*Real.log u) :=
    (hg u hu s hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  by_cases hfs : f s = 0
  · rw [hfs,norm_zero,Real.log_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg hD hE) hu0) hlogu
  have hl : Real.log C₁ ≤ E*Real.log u := by
    calc
      _ = E*Real.log 2 := by dsimp [E]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hu) hE
  calc
    _ ≤ Real.log (C₁*Real.exp (D*u*Real.log u)) := Real.log_le_log (norm_pos_iff.mpr hfs) hCf
    _ = Real.log C₁+D*u*Real.log u := by
      rw [Real.log_mul h₁.ne' (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ (D+E)*u*Real.log u := by
      have hh := mul_le_mul_of_nonneg_right (show 1 ≤ u by linarith)
        (mul_nonneg hE hlogu)
      nlinarith

theorem dirichlet_positive_strip_count {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (S : Finset (DirichletNontrivialZero χ)), 1 ≤ T →
      (∀ r ∈ S, |r.val.im| ≤ T) →
      (∑ r ∈ S, (analyticOrderNatAt (LFunction χ) r.val : ℝ)) ≤
        C*(T+2)*Real.log (T+2) := by
  classical
  let F := completedLFunction χ
  obtain ⟨C,hC,hG⟩ := jensen_growth_of_envelope (completed_dirichlet_envelope χ hχ)
  have h2 : F 2 ≠ 0 := completed_dirichlet_nonzero_of_one_le χ hχ (by norm_num)
  have ha (s : ℂ) : AnalyticAt ℂ F s := (differentiable_completedLFunction hχ).analyticAt s
  let D := ((6*C + |Real.log ‖F 2‖|/Real.log 2)/Real.log 2)
  have hlo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro T S hT hS
  let e : DirichletNontrivialZero χ ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  have h := jensen_strip_zero_count ha h2 C hC hG T hT (S.map e) (by
    intro s hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hs
    exact ⟨r.property.1.1.le,r.property.1.2.le,hS r hr⟩)
  simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) h
  intro r _
  change (analyticOrderNatAt (LFunction χ) r.val : ℝ) =
    (analyticOrderNatAt (completedLFunction χ) r.val : ℝ)
  unfold analyticOrderNatAt
  rw [completed_dirichlet_order r.property.1.1 hχ]

end RHConnections.DirichletZeroSet
