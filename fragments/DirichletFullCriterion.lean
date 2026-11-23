import Verified

open Filter
open scoped Topology
namespace RHConnections.DirichletZeroSet
open DirichletCharacter PoleCompensation

variable {N : ℕ} [NeZero N]

theorem dirichlet_fixed_strip_residual_iff (χ : DirichletCharacter ℂ N)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1/2) {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    (∀ z : ℂ, 1/2 < z.re →
      Tendsto (fun n => dirichletRestrictedResidual χ a n z z₀) atTop (𝓝 0)) ↔
    ∀ r : DirichletNontrivialZero χ, |r.val.re-1/2| ≤ a := by
  constructor
  · intro hres r
    have hfree {s : ℂ} (hs : a+1/2 < s.re) : LFunction χ s ≠ 0 :=
      dirichlet_zero_free_from_euler_residual χ hp hχ ha ha₁ hz₀ hres hs
    refine abs_le.mpr ⟨?_,?_⟩
    · by_contra! h
      have hdual := (primitive_strip_zero_reflection hp hχ r.property.1.1 r.property.1.2).mpr
        r.property.2
      apply hfree (s := 1-star r.val) _ hdual
      norm_num [Complex.sub_re]
      linarith
    · by_contra! h
      exact hfree (s := r.val) (by linarith) r.property.2
  · intro h z _
    exact dirichlet_residual_limit_of_containment χ hp hχ h z z₀

def DirichletGRH : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ),
    0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1/2

def PrimitiveLineEulerResidual (z₀ : ℂ) : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ.IsPrimitive → χ ≠ 1 →
    ∀ z : ℂ, 1/2 < z.re →
      Tendsto (fun n => dirichletRestrictedResidual χ 0 n z z₀) atTop (𝓝 0)

private theorem zeta_line_of_RH (hRH : RiemannHypothesis) {s : ℂ}
    (hp : 0 < s.re) (h1 : s.re < 1) (hs : riemannZeta s = 0) : s.re = 1/2 := by
  apply hRH s hs
  · rintro ⟨n,hn⟩
    have he := congrArg Complex.re hn
    simp [Complex.mul_re, Complex.add_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro he
    simpa [he] using h1

private theorem zeta_zero_of_principal_zero (χ : DirichletCharacter ℂ N)
    (hχ : χ = 1) {s : ℂ} (hp : 0 < s.re) (h1 : s.re < 1)
    (hs : LFunction χ s = 0) : riemannZeta s = 0 := by
  have hs₁ : s ≠ 1 := fun he => by simpa [he] using h1
  have hprod : (∏ p ∈ N.primeFactors, (1 - (p:ℂ)^(-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p h
    have hprime := Nat.prime_of_mem_primeFactors h
    have hpow : ‖(p:ℂ)^(-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_lt_zero.mpr hp)
    intro he
    have he' := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one] at he'
    exact (ne_of_lt hpow) he'.symm
  rw [hχ, ← LFunctionTrivChar, LFunctionTrivChar_eq_mul_riemannZeta hs₁, mul_eq_zero] at hs
  exact hs.resolve_left hprod

theorem dirichletGRH_iff_line_euler_residuals {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    DirichletGRH ↔ ZetaLineEulerResidual z₀ ∧ PrimitiveLineEulerResidual z₀ := by
  constructor
  · intro h
    refine ⟨(riemannHypothesis_iff_line_euler_residual hz₀).mp ?_, ?_⟩
    · apply riemannHypothesis_of_right_zero_free
      intro s hr hz
      by_cases hs : s.re < 1
      · have hp : 0 < s.re := by linarith
        have hl : LFunction (1:DirichletCharacter ℂ 1) s = 0 := by
          rw [LFunction_modOne_eq]
          exact hz
        have hc := h 1 (1:DirichletCharacter ℂ 1) s hp hs hl
        linarith
      · exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hs) hz
    · intro M ins χ hp hχ
      apply (dirichlet_fixed_strip_residual_iff χ hp hχ (a := 0) (by norm_num) (by norm_num) hz₀).mpr
      intro r
      simp [h M χ r.val r.property.1.1 r.property.1.2 r.property.2]
  · rintro ⟨hzeta,hprim⟩ M ins χ s hs hs' hz
    have hRH := (riemannHypothesis_iff_line_euler_residual hz₀).mpr hzeta
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    let φ := χ.primitiveCharacter
    have hp : φ.IsPrimitive := χ.primitiveCharacter_isPrimitive
    by_cases hφ : φ = 1
    · have hχ : χ = 1 := by
        rw [← χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from hφ,
          changeLevel_one]
      exact zeta_line_of_RH hRH hs hs' (zeta_zero_of_principal_zero χ hχ hs hs' hz)
    · have hf := (LFunction_primitive_nontrivial_zero_iff χ hs hs').mp hz
      let r : DirichletNontrivialZero φ := ⟨s,⟨hs,hs'⟩,hf⟩
      have h := (dirichlet_fixed_strip_residual_iff φ hp hφ (a := 0)
        (by norm_num) (by norm_num) hz₀).mp (hprim χ.conductor φ hp hφ) r
      have he := abs_le.mp h
      change -(0:ℝ) ≤ s.re-1/2 ∧ s.re-1/2 ≤ 0 at he
      linarith [he.1,he.2]

end RHConnections.DirichletZeroSet
