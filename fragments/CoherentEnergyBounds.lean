import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

noncomputable section
namespace RHConnections.CoherentEnergyBounds

def j (r : ℕ) : ℝ := ∏ p ∈ r.primeFactors, (1 - 1/(p:ℝ)^2)

private theorem factor_nonneg (r p : ℕ) (hp : p ∈ r.primeFactors) :
    0 ≤ 1 - 1/(p:ℝ)^2 := by
  have h : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (show 0 < (p:ℝ)^2 by positivity)).mpr
  nlinarith [sq_nonneg ((p : ℝ) - 1)]

theorem j_nonneg (r : ℕ) : 0 ≤ j r := Finset.prod_nonneg (factor_nonneg r)

theorem j_le_one (r : ℕ) : j r ≤ 1 := by
  have hprod (T : Finset ℕ) (hT : T ⊆ r.primeFactors) :
      (∏ p ∈ T, (1 - 1/(p:ℝ)^2)) ≤ 1 := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert p T hp ih =>
      have hsub : T ⊆ r.primeFactors := (Finset.subset_insert _ _).trans hT
      rw [Finset.prod_insert hp]
      calc
        _ ≤ 1 * 1 := mul_le_mul (sub_le_self _ (by positivity)) (ih hsub)
          (Finset.prod_nonneg fun q hq => factor_nonneg r q (hsub hq)) zero_le_one
        _ = _ := one_mul _
  exact hprod _ (fun _ h => h)

@[simp] theorem j_one : j 1 = 1 := by simp [j]

def indices (B X : ℕ) := (Finset.Icc 1 X).filter fun r => Nat.Coprime r B

def energy (S : ℕ → ℝ) (B X : ℕ) : ℝ :=
  ∑ r ∈ indices B X, j r * S (X/r)^2

theorem scalar_sq_le_energy (S : ℕ → ℝ) (B X : ℕ) (hX : 1 ≤ X) :
    S X ^ 2 ≤ energy S B X := by
  have hm : 1 ∈ indices B X := by simp [indices, hX]
  simpa only [j_one, Nat.div_one, one_mul, energy] using
    (Finset.single_le_sum (f := fun r => j r * S (X/r)^2)
      (fun r _ => mul_nonneg (j_nonneg r) (sq_nonneg _)) hm)

def pSeries (p : ℝ) : ℝ := ∑' r : ℕ, 1/(r:ℝ)^p

private theorem sq_rpow (x : ℝ) (hx : 0 ≤ x) (t : ℝ) :
    (x^t)^2 = x^(2*t) := by
  calc
    _ = (x^t)^(2:ℝ) := by norm_num
    _ = _ := by rw [← Real.rpow_mul hx, mul_comm t]

theorem energy_upper (S : ℕ → ℝ) (B X : ℕ) {A θ : ℝ} (hA : 0 ≤ A) (hθ : 1/2 < θ)
    (hS : ∀ k : ℕ, 1 ≤ k → |S k| ≤ A*(k:ℝ)^θ) :
    energy S B X ≤ A^2 * pSeries (2*θ) * (X:ℝ)^(2*θ) := by
  let T := indices B X
  have hp : Summable (fun r : ℕ => 1/(r:ℝ)^(2*θ)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hterm (r : ℕ) (hr : r ∈ T) :
      j r * S (X/r)^2 ≤ (A^2*(X:ℝ)^(2*θ))*(1/(r:ℝ)^(2*θ)) := by
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    have hr' : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
    have hnat : ((X/r : ℕ) : ℝ) ≤ (X:ℝ)/(r:ℝ) := by
      apply (le_div_iff₀ hr').mpr
      exact_mod_cast Nat.div_mul_le_self X r
    have harg : |S (X/r)| ≤ A*((X:ℝ)/(r:ℝ))^θ :=
      (hS _ (Nat.div_pos hi.2 (by omega))).trans <|
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnat (by linarith)) hA
    have hsquare := pow_le_pow_left₀ (abs_nonneg _) harg 2
    calc
      _ ≤ S (X/r)^2 := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (j_le_one r) (sq_nonneg (S (X/r)))
      _ ≤ (A*((X:ℝ)/(r:ℝ))^θ)^2 := by simpa only [sq_abs] using hsquare
      _ = _ := by
        rw [mul_pow, sq_rpow _ (div_nonneg (Nat.cast_nonneg X) hr'.le),
          Real.div_rpow (Nat.cast_nonneg X) hr'.le]
        ring
  calc
    energy S B X ≤ ∑ r ∈ T, (A^2*(X:ℝ)^(2*θ))*(1/(r:ℝ)^(2*θ)) := Finset.sum_le_sum hterm
    _ = (A^2*(X:ℝ)^(2*θ)) * ∑ r ∈ T, 1/(r:ℝ)^(2*θ) := by rw [Finset.mul_sum]
    _ ≤ (A^2*(X:ℝ)^(2*θ))*pSeries (2*θ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hp.sum_le_tsum T (fun _ _ => by positivity)
    _ = _ := by ring

theorem all_epsilon_iff (S : ℕ → ℝ) (B : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 ≤ A ∧
      ∀ X : ℕ, 1 ≤ X → |S X| ≤ A*(X:ℝ)^(1/2+ε)) ↔
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 1 ≤ X → energy S B X ≤ C*(X:ℝ)^(1+δ)) := by
  constructor
  · intro h δ hδ
    obtain ⟨A,hA,hS⟩ := h (δ/2) (by positivity)
    have he : 2*(1/2+δ/2) = 1+δ := by ring
    refine ⟨A^2 * pSeries (1+δ), mul_nonneg (sq_nonneg _) (tsum_nonneg (fun _ => by positivity)), ?_⟩
    intro X _
    simpa only [he] using energy_upper S B X hA (show 1/2 < 1/2+δ/2 by linarith) hS
  · intro h ε hε
    obtain ⟨C,hC,hE⟩ := h (2*ε) (by positivity)
    refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
    intro X hX
    have hb := (scalar_sq_le_energy S B X hX).trans (hE X hX)
    have ht : (Real.sqrt C * (X:ℝ)^(1/2+ε))^2 = C*(X:ℝ)^(1+2*ε) := by
      rw [mul_pow, Real.sq_sqrt hC, sq_rpow _ (Nat.cast_nonneg X), show 2*(1/2+ε)=1+2*ε by ring]
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, ht]; exact hb

end RHConnections.CoherentEnergyBounds
