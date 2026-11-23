import Verified
import CoherentEnergyMeasure
import CoherentEnergyRHBridge

/-!
# Statement pins

Independent restatements of the headline results, written only in Mathlib's own terms.

* Every object below (the Mertens function, saphir's scalar, the weights, the energy, the
  Poisson measure and the phasor polynomial) is defined here from scratch, without using any
  definition from this repository.
* Every `theorem` is stated with these definitions and Mathlib's `_root_.RiemannHypothesis` and
  `riemannZeta`, and is proved by appeal to the repository's theorems.

Each pin states a headline result independently in Mathlib terms, and Lean checks that the
development proves that statement. The kernel replays check the proofs; the pins check that
what is proved is the statement written here.
-/

open Filter MeasureTheory

namespace StatementPins

/-! ## Independent definitions -/

/-- The Mertens function `M(n) = Σ_{1 ≤ j ≤ n} μ(j)`. -/
noncomputable def mertensFn (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius j : ℝ)

/-- saphir's scalar `S_B(n) = Σ_{k ≤ n, gcd(k,B) = 1} M(⌊n/k⌋) / k`. -/
noncomputable def scalar (B n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k B), mertensFn (n / k) / (k : ℝ)

/-- The weights `j(r) = ∏_{p | r} (1 - p⁻²)`. -/
noncomputable def weight (r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2)

/-- The coherent energy `Σ_{r ≤ X, gcd(r,B) = 1} j(r) S_B(⌊X/r⌋)²`. -/
noncomputable def energy (B X : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 X).filter (fun r => Nat.Coprime r B), weight r * scalar B (X / r) ^ 2

/-- On the circle of a prime `p`: the Poisson law with radius `1/p`. -/
noncomputable def poisson (p : ℕ) : Measure ℝ :=
  if p.Prime then
    (volume.restrict (Set.Ioc 0 (2 * Real.pi))).withDensity fun θ =>
      ENNReal.ofReal ((2 * Real.pi)⁻¹ *
        ((1 - ((p : ℝ)⁻¹) ^ 2) / (1 - 2 * (p : ℝ)⁻¹ * Real.cos θ + ((p : ℝ)⁻¹) ^ 2)))
  else Measure.dirac 0

/-- The product measure `ν = ⊗_p ν_p`. -/
noncomputable def nu : Measure (ℕ → ℝ) := Measure.infinitePi poisson

/-- `Z(d) = ∏_p z_p^{v_p(d)}` with `z_p = e^{i θ_p}`. -/
noncomputable def phasorMonomial (d : ℕ) (θ : ℕ → ℝ) : ℂ :=
  ∏ p ∈ d.primeFactors, Complex.exp (Complex.I * (θ p : ℂ)) ^ d.factorization p

/-- The inclusion–exclusion window `w_{X,B}(n) = Σ_{b | rad B} μ(b) 1_{n ≤ X/b}`. -/
noncomputable def window (B X n : ℕ) : ℝ :=
  ∑ b ∈ (∏ p ∈ B.primeFactors, p).divisors,
    if n ≤ X / b then (ArithmeticFunction.moebius b : ℝ) else 0

/-- `D_{X,B} = Σ_{n ≤ X, gcd(n,B) = 1} w_{X,B}(n) Σ_{d | n} μ(n/d) Z(d)`. -/
noncomputable def poly (B X : ℕ) (θ : ℕ → ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n B),
    (window B X n : ℂ) *
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℂ) * phasorMonomial d θ

/-! ## The independent definitions agree with the repository's -/

theorem nu_eq : nu = RHConnections.CoherentEnergyMeasure.primeTorusMeasure := rfl

theorem poly_eq (B X : ℕ) : poly B X = RHConnections.CoherentEnergyMeasure.D B X := rfl

theorem mertensFn_eq (n : ℕ) : mertensFn n = RHConnections.CoherentEnergyMeasure.mertens n := by
  unfold mertensFn RHConnections.CoherentEnergyMeasure.mertens
  have h : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]

theorem scalar_eq (B n : ℕ) : scalar B n = RHConnections.ArithmeticFourierInversion.S B n := by
  rw [← RHConnections.CoherentEnergyMeasure.scalarS_eq_S]
  unfold scalar RHConnections.CoherentEnergyMeasure.scalarS
  simp only [mertensFn_eq]

theorem energy_eq (B X : ℕ) :
    energy B X = RHConnections.CoherentEnergyBounds.energy
      (RHConnections.ArithmeticFourierInversion.S B) B X := by
  unfold energy RHConnections.CoherentEnergyBounds.energy RHConnections.CoherentEnergyBounds.indices
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [scalar_eq]
  rfl

/-! ## Headline results, pinned -/

/-- Saphir's inverse: `M(n) = Σ_{k ≤ n, gcd(k,B)=1} μ(k)/k · S_B(⌊n/k⌋)`. -/
theorem pin_inverse (B n : ℕ) :
    mertensFn n = ∑ k ∈ Finset.Ioc 0 n,
      (if Nat.Coprime k B then (ArithmeticFunction.moebius k : ℝ) / k else 0) * scalar B (n / k) := by
  rw [mertensFn_eq, RHConnections.CoherentEnergyMeasure.mertens_eq_M,
    RHConnections.ArithmeticFourierInversion.M_from_S]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RHConnections.ArithmeticFourierInversion.h_apply, scalar_eq]

/-- The energy identity: `‖D_{X,B}‖²_ν = Σ j(r) S_B(⌊X/r⌋)²` for every `B ≥ 1`. -/
theorem pin_energy_identity {B : ℕ} (hB : 1 ≤ B) (X : ℕ) :
    ∫ θ, ‖poly B X θ‖ ^ 2 ∂nu = energy B X := by
  rw [nu_eq, poly_eq, energy_eq]
  exact RHConnections.CoherentEnergyMeasure.norm_sq_D_eq_coherent_energy hB X

/-- RH holds iff the coherent energy grows at most like `X^{1+δ}` for every `δ > 0`. -/
theorem pin_rh_iff_energy (B : ℕ) :
    _root_.RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X → energy B X ≤ C * (X : ℝ) ^ (1 + δ) := by
  simp_rw [energy_eq]
  exact (RHConnections.ArithmeticFourierInversion.coherent_energy_growth_iff_RH B).symm

/-- RH holds iff the squared norm of the phasor polynomial grows at most like `X^{1+δ}`. -/
theorem pin_rh_iff_norm {B : ℕ} (hB : 1 ≤ B) :
    _root_.RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
        ∫ θ, ‖poly B X θ‖ ^ 2 ∂nu ≤ C * (X : ℝ) ^ (1 + δ) := by
  rw [nu_eq]
  simp_rw [poly_eq]
  exact (RHConnections.CoherentEnergyMeasure.coherent_energy_measure_growth_iff_RH hB).symm

/-- For either fixed sign `σ`: RH holds iff eventually `σ S_B(n) ≥ -C n^{1/2+ε}` for every `ε > 0`. -/
theorem pin_rh_iff_one_sided (B : ℕ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    _root_.RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ n : ℕ in atTop, -(C * (n : ℝ) ^ (1 / 2 + ε)) ≤ σ * scalar B n := by
  simp_rw [scalar_eq]
  exact RHConnections.ArithmeticFourierInversion.rh_iff_one_sided_fourier_scalar B hσ

/-- A zero-free half-plane `Re s > a` holds iff `S_B(n) = O(n^{a+ε})` for every `ε > 0`. -/
theorem pin_strip_iff_scalar (B : ℕ) {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    (∀ s : ℂ, a < s.re → riemannZeta s ≠ 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |scalar B n| ≤ C * (n : ℝ) ^ (a + ε) := by
  simp_rw [scalar_eq]
  exact RHConnections.ArithmeticFourierInversion.fixed_strip_iff_fourier_scalar_power B ha ha1

/-- The classical criterion, both directions: RH iff `M(x) = O(x^{1/2+ε})` for every `ε > 0`. -/
theorem pin_rh_iff_mertens :
    _root_.RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun x : ℝ => ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ))
          =O[atTop] (fun x : ℝ => x ^ (1 / 2 + ε)) :=
  RHConnections.MertensCriterion.mertens_cancellation_iff_RH.symm

end StatementPins

#print axioms StatementPins.pin_inverse
#print axioms StatementPins.pin_energy_identity
#print axioms StatementPins.pin_rh_iff_energy
#print axioms StatementPins.pin_rh_iff_norm
#print axioms StatementPins.pin_rh_iff_one_sided
#print axioms StatementPins.pin_strip_iff_scalar
#print axioms StatementPins.pin_rh_iff_mertens
