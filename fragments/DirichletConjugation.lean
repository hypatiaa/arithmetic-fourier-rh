import Verified
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.MulChar.Lemmas

noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter Complex Filter
open scoped ComplexConjugate Topology

variable {N : ℕ} [NeZero N]

theorem LFunction_conj_euler (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    conj (LFunction χ (conj s)) = LFunction χ⁻¹ s := by
  rw [LFunction_eq_LSeries χ (by simpa using hs), LFunction_eq_LSeries χ⁻¹ hs]
  simp only [LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp [LSeries.term]
  · simp only [LSeries.term, if_neg hn, map_div₀]
    have hc : conj (χ (n : ZMod N)) = χ⁻¹ (n : ZMod N) := MulChar.star_apply' χ _
    have harg : (n:ℂ).arg ≠ Real.pi := by simp [Real.pi_ne_zero.symm]
    rw [hc, ← Complex.conj_cpow _ _ harg]
    simp

private theorem entire_conj_uniq {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (ha : ∀ s : ℂ, 1 < s.re → conj (f (conj s)) = g s) (s : ℂ) :
    conj (f (conj s)) = g s := by
  let h := fun t : ℂ => conj (f (conj t))
  have hd : Differentiable ℂ h := by
    intro t
    change DifferentiableAt ℂ (conj ∘ f ∘ conj) t
    exact differentiableAt_conj_conj_iff.mpr (hf (conj t))
  have hh : AnalyticOnNhd ℂ h Set.univ := fun t _ => hd.analyticAt t
  have h2 : {t : ℂ | 1 < t.re} ∈ 𝓝 (2:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he := hh.eq_of_eventuallyEq (fun t _ => hg.analyticAt t)
    (Filter.Eventually.mono h2 (fun t ht => ha t ht))
  exact congrFun he s

theorem LFunction_conj_inverse {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    conj (LFunction χ (conj s)) = LFunction χ⁻¹ s :=
  entire_conj_uniq (differentiable_LFunction hχ)
    (differentiable_LFunction (fun h => hχ (inv_eq_one.mp h))) (fun _ => LFunction_conj_euler χ) s

private theorem gammaReal_conj (s : ℂ) : conj (Complex.Gammaℝ (conj s)) = Complex.Gammaℝ s := by
  have harg : ((Real.pi:ℝ):ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have he : -(conj s)/2 = conj (-s/2) := by rw [map_div₀, map_neg, Complex.conj_ofNat 2]
  have he' : conj s/2 = conj (s/2) := by rw [map_div₀, Complex.conj_ofNat 2]
  simp only [Complex.Gammaℝ_def, map_mul, he, he', Complex.Gamma_conj, Complex.conj_conj]
  rw [← Complex.conj_cpow _ _ harg, Complex.conj_ofReal]

theorem gammaFactor_conj_inverse (χ : DirichletCharacter ℂ N) (s : ℂ) :
    conj (gammaFactor χ (conj s)) = gammaFactor χ⁻¹ s := by
  rcases χ.even_or_odd with he|ho
  · have hi : (χ⁻¹).Even := by
      change χ⁻¹ (-1) = 1
      rw [MulChar.inv_apply_eq_inv', show χ (-1) = 1 from he, inv_one]
    rw [he.gammaFactor_def, hi.gammaFactor_def, gammaReal_conj]
  · have hi : (χ⁻¹).Odd := by
      change χ⁻¹ (-1) = -1
      rw [MulChar.inv_apply_eq_inv', show χ (-1) = -1 from ho]; simp
    rw [ho.gammaFactor_def, hi.gammaFactor_def, show conj s+1=conj (s+1) by simp,
      gammaReal_conj]

theorem completedLFunction_conj_inverse {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    conj (completedLFunction χ (conj s)) = completedLFunction χ⁻¹ s := by
  apply entire_conj_uniq (differentiable_completedLFunction hχ)
    (differentiable_completedLFunction (fun h => hχ (inv_eq_one.mp h))) _ s
  intro t ht
  have ht0 : 0 < t.re := by linarith
  rw [(completed_dirichlet_germ χ (s := conj t) (by simpa using ht0)).eq_of_nhds,
    (completed_dirichlet_germ χ⁻¹ ht0).eq_of_nhds, map_mul,
    gammaFactor_conj_inverse, LFunction_conj_inverse hχ]

theorem primitive_completed_reflection {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (s : ℂ) :
    completedLFunction χ (1-conj s) =
      (N:ℂ)^(conj s-1/2) * rootNumber χ * conj (completedLFunction χ s) := by
  rw [hp.completedLFunction_one_sub, ← completedLFunction_conj_inverse hχ, Complex.conj_conj]

theorem primitive_completed_zero_reflection {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (s : ℂ) :
    completedLFunction χ (1-conj s) = 0 ↔ completedLFunction χ s = 0 := by
  have hn : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hpow : (N:ℂ)^(conj s-1/2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn]; exact Complex.exp_ne_zero _
  rw [primitive_completed_reflection hp hχ]
  rw [mul_eq_zero]
  simp only [(mul_ne_zero hpow (primitive_rootNumber_nonzero hp hχ)), false_or]
  simp

theorem primitive_strip_zero_reflection {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) {s : ℂ} (hl : 0 < s.re) (hr : s.re < 1) :
    LFunction χ (1-conj s) = 0 ↔ LFunction χ s = 0 := by
  have h := primitive_completed_zero_reflection hp hχ s
  rw [completed_dirichlet_zero_iff hp hχ, completed_dirichlet_zero_iff hp hχ] at h
  simpa [Complex.sub_re, hl, hr, sub_pos.mpr hr, show 1-s.re < 1 by linarith] using h

end RHConnections.DirichletZeroSet
