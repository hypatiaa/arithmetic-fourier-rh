import Verified
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open Filter
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def removedEulerFactors (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ)^(-s))

theorem removed_euler_factor_nonzero {s : ℂ} (hs : 0 < s.re)
    {p : ℕ} (hp : p.Prime) :
    1 - χ.primitiveCharacter (p:ZMod χ.conductor) * (p:ℂ)^(-s) ≠ 0 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hn : ‖(p:ℂ)^(-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.mpr hs)
  have hb := χ.primitiveCharacter.norm_le_one (p:ZMod χ.conductor)
  have he : ‖χ.primitiveCharacter (p:ZMod χ.conductor) * (p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans_lt hn
  intro h
  have hh := congrArg norm ((sub_eq_zero.mp h).symm)
  rw [norm_one] at hh
  exact (ne_of_lt he) hh

theorem removedEulerFactors_nonzero {s : ℂ} (hs : 0 < s.re) :
    removedEulerFactors χ s ≠ 0 := by
  unfold removedEulerFactors
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact removed_euler_factor_nonzero χ hs (Nat.prime_of_mem_primeFactors hp)

theorem removedEulerFactors_entire : Differentiable ℂ (removedEulerFactors χ) := by
  unfold removedEulerFactors
  apply Differentiable.fun_finsetProd
  intro p hp
  haveI : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  fun_prop

theorem LFunction_primitive_factorization {s : ℂ} (hs : s ≠ 1) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    LFunction χ s = LFunction χ.primitiveCharacter s * removedEulerFactors χ s := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter] at h
  exact h

theorem LFunction_primitive_order {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    analyticOrderAt (LFunction χ) s = analyticOrderAt (LFunction χ.primitiveCharacter) s := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hEq : LFunction χ =ᶠ[nhds s] (LFunction χ.primitiveCharacter * removedEulerFactors χ) := by
    filter_upwards [eventually_ne_nhds hs₁] with t ht
    exact LFunction_primitive_factorization χ ht
  have hL : AnalyticAt ℂ (LFunction χ.primitiveCharacter) s := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hD : DifferentiableOn ℂ (LFunction χ.primitiveCharacter) ({1}ᶜ : Set ℂ) :=
      fun t ht => (differentiableAt_LFunction _ t (Or.inl ht)).differentiableWithinAt
    exact hD.analyticOnNhd hU s hs₁
  have hE := (removedEulerFactors_entire χ).analyticAt s
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hL hE,
    analyticOrderAt_eq_zero.mpr (Or.inr (removedEulerFactors_nonzero χ hs)), add_zero]

theorem LFunction_primitive_nontrivial_zero_iff {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs₁ : s ≠ 1 := fun he => by simpa [he] using hs'
  rw [LFunction_primitive_factorization χ hs₁, mul_eq_zero]
  simp [removedEulerFactors_nonzero χ hs]

end RHConnections.DirichletZeroSet
