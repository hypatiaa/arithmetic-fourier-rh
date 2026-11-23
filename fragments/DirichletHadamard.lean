import Verified

open Filter
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter SpectralTail EntireCanonicalProduct

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def normalizedCompletedDirichlet (s : ℂ) : ℂ :=
  (completedLFunction χ 0)⁻¹ * completedLFunction χ s

theorem completed_dirichlet_zero_value_nonzero (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    completedLFunction χ 0 ≠ 0 := fun hz => by
  have h := (completed_dirichlet_zero_iff hp hχ 0).mp hz
  simpa only [Complex.zero_re, lt_self_iff_false] using h.1.1

theorem normalized_completed_at_zero (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    normalizedCompletedDirichlet χ 0 = 1 :=
  inv_mul_cancel₀ (completed_dirichlet_zero_value_nonzero χ hp hχ)

theorem normalized_completed_entire (hχ : χ ≠ 1) (s : ℂ) :
    AnalyticAt ℂ (normalizedCompletedDirichlet χ) s :=
  analyticAt_const.mul ((differentiable_completedLFunction hχ).analyticAt s)

theorem normalized_completed_zero_iff (hp : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    normalizedCompletedDirichlet χ s = 0 ↔ (0 < s.re ∧ s.re < 1) ∧ LFunction χ s = 0 := by
  rw [normalizedCompletedDirichlet, mul_eq_zero]
  simp [inv_ne_zero (completed_dirichlet_zero_value_nonzero χ hp hχ),
    completed_dirichlet_zero_iff hp hχ s]

theorem normalized_completed_order (hp : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    analyticOrderAt (normalizedCompletedDirichlet χ) s = analyticOrderAt (LFunction χ) s := by
  have hC : AnalyticAt ℂ (fun _ : ℂ => (completedLFunction χ 0)⁻¹) s := analyticAt_const
  have hC0 : analyticOrderAt (fun _ : ℂ => (completedLFunction χ 0)⁻¹) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero (completed_dirichlet_zero_value_nonzero χ hp hχ)))
  change analyticOrderAt ((fun _ => (completedLFunction χ 0)⁻¹) * completedLFunction χ) s = _
  rw [analyticOrderAt_mul hC ((differentiable_completedLFunction hχ).analyticAt s),
    hC0, zero_add, completed_dirichlet_order hs hχ]

def normalized_dirichlet_zero_equiv (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ZeroOf (normalizedCompletedDirichlet χ) ≃ DirichletNontrivialZero χ where
  toFun r := ⟨r.val, (normalized_completed_zero_iff χ hp hχ r.val).mp r.property⟩
  invFun r := ⟨r.val, (normalized_completed_zero_iff χ hp hχ r.val).mpr r.property⟩
  left_inv r := Subtype.ext rfl
  right_inv r := Subtype.ext rfl

theorem normalized_dirichlet_count (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (S : Finset (ZeroOf (normalizedCompletedDirichlet χ))), 1 ≤ T →
      (∀ r ∈ S, |r.val.im| ≤ T) →
      (∑ r ∈ S, (analyticOrderNatAt (normalizedCompletedDirichlet χ) r.val : ℝ)) ≤
        C*(T+2)*Real.log (T+2) := by
  obtain ⟨C,hC,hc⟩ := dirichlet_positive_strip_count χ hχ
  refine ⟨C,hC,?_⟩
  intro T S hT hS
  let e := (normalized_dirichlet_zero_equiv χ hp hχ).toEmbedding
  have h := hc T (S.map e) hT (by
    intro r hr
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hr
    exact hS q hq)
  rw [Finset.sum_map] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) h
  intro r _
  have hr := (normalized_completed_zero_iff χ hp hχ r.val).mp r.property
  change (analyticOrderNatAt (normalizedCompletedDirichlet χ) r.val : ℝ) =
    (analyticOrderNatAt (LFunction χ) r.val : ℝ)
  simp only [analyticOrderNatAt, normalized_completed_order χ hp hχ hr.1.1]

private theorem normalized_dirichlet_norm_lower (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ZeroOf (normalizedCompletedDirichlet χ), δ ≤ ‖r.val‖ := by
  have hF : normalizedCompletedDirichlet χ 0 ≠ 0 :=
    (normalized_completed_at_zero χ hp hχ).trans_ne one_ne_zero
  have hnear := (normalized_completed_entire χ hχ 0).continuousAt.eventually_ne hF
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ,hδ,fun r => le_of_not_gt fun h => ?_⟩
  exact hh (show dist r.val (0:ℂ) < δ by simpa only [dist_zero_right] using h) r.property

theorem normalized_dirichlet_three_halves (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun r : RepeatedZeroOf (normalizedCompletedDirichlet χ) =>
      1/(‖r.1.val‖*Real.sqrt ‖r.1.val‖)) := by
  let F := normalizedCompletedDirichlet χ
  obtain ⟨δ,hδ,hδ'⟩ := normalized_dirichlet_norm_lower χ hp hχ
  obtain ⟨C,hC,hc⟩ := normalized_dirichlet_count χ hp hχ
  exact inverse_three_halves_repeated (fun r : ZeroOf F => r.val)
    (fun r => analyticOrderNatAt F r.val) hδ hδ' hC hc

def dirichletProductData (hp : χ.IsPrimitive) (hχ : χ ≠ 1) : Data where
  F := normalizedCompletedDirichlet χ
  entire := fun s _ => normalized_completed_entire χ hχ s
  at_zero := normalized_completed_at_zero χ hp hχ
  square_summable := by
    obtain ⟨δ,hδ,hδ'⟩ := normalized_dirichlet_norm_lower χ hp hχ
    have hg := (normalized_dirichlet_three_halves χ hp hχ).mul_left (1/Real.sqrt δ)
    apply hg.of_nonneg_of_le (fun _ => by positivity)
    intro r
    have h := hδ' r.1
    have hρ := hδ.trans_le h
    have hδs := Real.sqrt_pos.mpr hδ
    have hρs := Real.sqrt_pos.mpr hρ
    rw [div_mul_div_comm, one_mul]
    apply (div_le_div_iff₀ (sq_pos_of_pos hρ) (by positivity)).mpr
    rw [one_mul]
    calc
      _ ≤ (Real.sqrt ‖r.1.val‖) * (‖r.1.val‖ * Real.sqrt ‖r.1.val‖) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (by positivity)
      _ = _ := by nlinarith only [congrArg (fun t : ℝ => ‖r.1.val‖ * t) (Real.sq_sqrt hρ.le)]

theorem dirichlet_hadamard (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    (dirichletProductData χ hp hχ).HadamardFactorization :=
  (dirichletProductData χ hp hχ).hadamard_factorization
    ((completed_dirichlet_envelope χ hχ).const_mul _)
    (normalized_dirichlet_three_halves χ hp hχ)

end RHConnections.DirichletZeroSet
