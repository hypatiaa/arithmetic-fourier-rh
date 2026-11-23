import Verified

open MeasureTheory
open scoped Classical
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter DirichletGeometricLimit PoleCompensation

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem compact_prime_sum_summable {f : ℝ → ℂ} (hf : HasCompactSupport f) (a : ℕ → ℂ) :
    Summable (fun m : ℕ => a m*f (Real.log m)) := by
  obtain ⟨R,hR⟩ := (show IsCompact (tsupport f) from hf).bddAbove
  let K := Finset.range (⌊Real.exp R⌋₊ + 1)
  apply summable_of_ne_finset_zero (s := K)
  intro m hm
  have hn : ⌊Real.exp R⌋₊ < m := by
    simpa [K, Finset.mem_range] using hm
  have hlt : Real.exp R < (m:ℝ) := (Nat.floor_lt (Real.exp_pos R).le).mp hn
  have hml : R < Real.log (m:ℝ) := (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hlt)).2 hlt
  have hz : f (Real.log m) = 0 := by
    by_contra hz
    have hm : Real.log (m:ℝ) ∈ tsupport f := subset_tsupport f hz
    exact (not_le_of_gt hml) (hR hm)
  rw [hz,mul_zero]

theorem halfWeight_primitive_on_unit (m : ℕ) (hm : IsUnit (m : ZMod N)) :
    halfWeight χ m = halfWeight χ.primitiveCharacter m := by
  have hcop := (ZMod.isUnit_iff_coprime m N).mp hm
  have he : χ.primitiveCharacter (m : ZMod χ.conductor) = χ (m : ZMod N) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr hcop)
  by_cases h0 : m = 0
  · simp [h0,halfWeight]
  · simp [halfWeight, LSeries.term_of_ne_zero h0, he]

def omittedPrimeTest (f : ℝ → ℂ) : ℂ :=
  ∑' m : ℕ, (if IsUnit (m:ZMod N) then 0 else halfWeight χ.primitiveCharacter m)*f (Real.log m)

theorem primitive_prime_test_split {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    (∑' m : ℕ, halfWeight χ.primitiveCharacter m*f (Real.log m)) =
      (∑' m : ℕ, halfWeight χ m*f (Real.log m)) + omittedPrimeTest χ f := by
  unfold omittedPrimeTest
  rw [← (compact_prime_sum_summable hf _).tsum_add (compact_prime_sum_summable hf _)]
  apply tsum_congr
  intro m
  by_cases hm : IsUnit (m : ZMod N)
  · simp [hm,halfWeight_primitive_on_unit χ m hm]
  · simp [hm,halfWeight_zero_of_nonunit χ m hm]

theorem imprimitive_explicit_formula_nonprincipal (hχ : χ ≠ 1)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    ((∑' m : ℕ, halfWeight χ m * f (Real.log m)) + omittedPrimeTest χ f) +
      (∫ x in Set.Ioi (0:ℝ),
        (parityRealPlaceKernel (if χ.primitiveCharacter.Even then false else true) x:ℂ)*f x) =
      -(∑' r : DirichletNontrivialZero χ, (analyticOrderNatAt (LFunction χ) r.val : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let φ := χ.primitiveCharacter
  have hφ : φ ≠ 1 := fun he => hχ (by
    rw [← χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from he,
      changeLevel_one])
  let e : DirichletNontrivialZero χ ≃ DirichletNontrivialZero φ :=
    { toFun := fun r => ⟨r.val, r.property.1,
        (LFunction_primitive_nontrivial_zero_iff χ r.property.1.1 r.property.1.2).mp r.property.2⟩
      invFun := fun r => ⟨r.val, r.property.1,
        (LFunction_primitive_nontrivial_zero_iff χ r.property.1.1 r.property.1.2).mpr r.property.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  rw [← primitive_prime_test_split χ hc]
  have h := dirichlet_explicit_formula_compact φ χ.primitiveCharacter_isPrimitive hφ f hf hc hzero
  rw [← e.tsum_eq] at h
  refine h.trans (congrArg Neg.neg (tsum_congr fun r => ?_))
  have hr : r.val ≠ 1 := fun he => by
    have h := r.property.1.2
    simpa [he] using h
  have horder := congrArg ENat.toNat (LFunction_primitive_order χ r.property.1.1 hr)
  change analyticOrderNatAt (LFunction χ) r.val = analyticOrderNatAt (LFunction φ) r.val at horder
  change (analyticOrderNatAt (LFunction φ) r.val : ℂ) * _ =
    (analyticOrderNatAt (LFunction χ) r.val : ℂ) * _
  rw [horder]
  rfl

def omittedPrincipalPrimeTest (N : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑' m : ℕ, (if IsUnit (m:ZMod N) then 0 else EulerGeometricLimit.halfWeight m)*f (Real.log m)

theorem principal_prime_test_split (N : ℕ) {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    (∑' m : ℕ, EulerGeometricLimit.halfWeight m*f (Real.log m)) =
      (∑' m : ℕ, halfWeight (1:DirichletCharacter ℂ N) m*f (Real.log m)) +
      omittedPrincipalPrimeTest N f := by
  unfold omittedPrincipalPrimeTest
  rw [← (compact_prime_sum_summable hf _).tsum_add (compact_prime_sum_summable hf _)]
  apply tsum_congr
  intro m
  by_cases hm : IsUnit (m : ZMod N)
  · have he : (1 : DirichletCharacter ℂ N) (m:ZMod N) = 1 := MulChar.one_apply hm
    have hχ : halfWeight (1 : DirichletCharacter ℂ N) m = EulerGeometricLimit.halfWeight m := by
      by_cases h0 : m = 0
      · simp [h0,halfWeight,EulerGeometricLimit.halfWeight]
      · simp [halfWeight,EulerGeometricLimit.halfWeight,LSeries.term_of_ne_zero h0,he]
    simp [hm,hχ]
  · simp [hm,halfWeight_zero_of_nonunit (1 : DirichletCharacter ℂ N) m hm]

theorem principal_dirichlet_explicit_formula_compact (N : ℕ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    ((∑' m : ℕ, halfWeight (1:DirichletCharacter ℂ N) m*f (Real.log m)) +
      omittedPrincipalPrimeTest N f) +
        (∫ x in Set.Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*f x) =
      (∫ x in Set.Ioi (0:ℝ), Complex.exp ((1/2:ℂ)*(x:ℂ))*f x) +
      (∫ x in Set.Ioi (0:ℝ), Complex.exp ((-1/2:ℂ)*(x:ℂ))*f x) -
      (∑' r : SpectralTail.NontrivialZetaZero, (analyticOrderNatAt riemannZeta r.val : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x) := by
  rw [← principal_prime_test_split N hc]
  exact zeta_explicit_formula_compact f hf hc hzero

end RHConnections.DirichletZeroSet
