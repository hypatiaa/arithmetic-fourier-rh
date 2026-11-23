import RelativeResolvent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open MeasureTheory
open scoped Interval

namespace RHConnections.EndpointIBP

theorem transfer_derivative (u R : ℝ) {ρ dρ g dg : ℝ → ℂ}
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (hiρ : IntervalIntegrable (fun y => dρ (u-y)) volume 0 R)
    (hig : IntervalIntegrable dg volume 0 R) :
    (∫ y in (0:ℝ)..R, dρ (u-y) * g y) =
      ρ u * g 0 - ρ (u-R) * g R + ∫ y in (0:ℝ)..R, ρ (u-y) * dg y := by
  have hk (y : ℝ) : HasDerivAt (fun x => ρ (u-x)) (-(dρ (u-y))) y := by
    have hr : HasDerivAt (fun x : ℝ => u-x) (-1) y := by
      simpa [Pi.sub_apply, id_def] using! (hasDerivAt_const y u).sub (hasDerivAt_id y)
    simpa [Function.comp_def] using (hρ (u-y)).scomp y hr
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y _ => hk y) (fun y _ => hg y) hiρ.neg hig
  simp only [sub_zero, neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add] at h
  linear_combination -h

theorem first_transfer (u R : ℝ) {ρ dρ g dg : ℝ → ℂ}
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (hiρ : IntervalIntegrable (fun y => dρ (u-y)) volume 0 R)
    (hig : IntervalIntegrable dg volume 0 R)
    (hR : ρ (u-R) = 0) (h0 : g 0 = 0) :
    (∫ y in (0:ℝ)..R, dρ (u-y) * g y) = ∫ y in (0:ℝ)..R, ρ (u-y) * dg y := by
  simpa [hR, h0] using transfer_derivative u R hρ hg hiρ hig

theorem second_transfer (u R : ℝ) {ρ dρ ddρ g dg ddg : ℝ → ℂ}
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t) (hdρ : ∀ t, HasDerivAt dρ (ddρ t) t)
    (hg : ∀ t, HasDerivAt g (dg t) t) (hdg : ∀ t, HasDerivAt dg (ddg t) t)
    (hiρ : IntervalIntegrable (fun y => dρ (u-y)) volume 0 R)
    (hidρ : IntervalIntegrable (fun y => ddρ (u-y)) volume 0 R)
    (hig : IntervalIntegrable dg volume 0 R) (hidg : IntervalIntegrable ddg volume 0 R)
    (hR : ρ (u-R) = 0) (hdR : dρ (u-R) = 0) (h0 : g 0 = 0) :
    (∫ y in (0:ℝ)..R, ddρ (u-y) * g y) =
      ρ u * dg 0 + ∫ y in (0:ℝ)..R, ρ (u-y) * ddg y := by
  rw [first_transfer u R hdρ hg hidρ hig hdR h0]
  simpa [hR] using transfer_derivative u R hρ hdg hiρ hidg

noncomputable section

def positiveBranch (z z₀ : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-z * (y:ℂ)) - Complex.exp (-z₀ * (y:ℂ))

def firstBranch (z z₀ : ℂ) (y : ℝ) : ℂ :=
  -z * Complex.exp (-z * (y:ℂ)) - (-z₀) * Complex.exp (-z₀ * (y:ℂ))

def secondBranch (z z₀ : ℂ) (y : ℝ) : ℂ :=
  z^2 * Complex.exp (-z * (y:ℂ)) - z₀^2 * Complex.exp (-z₀ * (y:ℂ))

private theorem exp_derivative (c : ℂ) (y : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * (x:ℂ)))
      (c * Complex.exp (c * (y:ℂ))) y := by
  simpa [mul_comm] using (((hasDerivAt_id (y:ℂ)).const_mul c).cexp).comp_ofReal

theorem positiveBranch_derivative (z z₀ : ℂ) (y : ℝ) :
    HasDerivAt (positiveBranch z z₀) (firstBranch z z₀ y) y :=
  (exp_derivative (-z) y).sub (exp_derivative (-z₀) y)

theorem firstBranch_derivative (z z₀ : ℂ) (y : ℝ) :
    HasDerivAt (firstBranch z z₀) (secondBranch z z₀ y) y := by
  convert ((exp_derivative (-z) y).const_mul (-z)).sub
    ((exp_derivative (-z₀) y).const_mul (-z₀)) using 1 <;>
    first | rfl | (unfold secondBranch; ring)

theorem exponential_transfers (u R : ℝ) (z z₀ : ℂ) {ρ dρ ddρ : ℝ → ℂ}
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t) (hdρ : ∀ t, HasDerivAt dρ (ddρ t) t)
    (hiρ : IntervalIntegrable (fun y => dρ (u-y)) volume 0 R)
    (hidρ : IntervalIntegrable (fun y => ddρ (u-y)) volume 0 R)
    (hR : ρ (u-R) = 0) (hdR : dρ (u-R) = 0) :
    (∫ y in (0:ℝ)..R, dρ (u-y) * positiveBranch z z₀ y) =
      (∫ y in (0:ℝ)..R, ρ (u-y) * firstBranch z z₀ y) ∧
    (∫ y in (0:ℝ)..R, ddρ (u-y) * positiveBranch z z₀ y) =
      ρ u * (z₀-z) + ∫ y in (0:ℝ)..R, ρ (u-y) * secondBranch z z₀ y := by
  have h0 : positiveBranch z z₀ 0 = 0 := by simp [positiveBranch]
  have hd0 : firstBranch z z₀ 0 = z₀-z := by simp [firstBranch]; ring
  have h₁ : Continuous (firstBranch z z₀) := by unfold firstBranch; fun_prop
  have h₂ : Continuous (secondBranch z z₀) := by unfold secondBranch; fun_prop
  exact ⟨first_transfer u R hρ (positiveBranch_derivative z z₀) hiρ
      (h₁.intervalIntegrable 0 R) hR h0,
    hd0 ▸ second_transfer u R hρ hdρ (positiveBranch_derivative z z₀)
      (firstBranch_derivative z z₀) hiρ hidρ (h₁.intervalIntegrable 0 R)
      (h₂.intervalIntegrable 0 R) hR hdR h0⟩

theorem logTest_second_transfer (u R : ℝ) (hR0 : 0 ≤ R) (z z₀ : ℂ)
    {ρ dρ ddρ : ℝ → ℂ}
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t) (hdρ : ∀ t, HasDerivAt dρ (ddρ t) t)
    (hiρ : IntervalIntegrable (fun y => dρ (u-y)) volume 0 R)
    (hidρ : IntervalIntegrable (fun y => ddρ (u-y)) volume 0 R)
    (hR : ρ (u-R) = 0) (hdR : dρ (u-R) = 0) :
    (∫ y in (0:ℝ)..R, ddρ (u-y) * RelativeResolvent.logTest z z₀ y) =
      ρ u * (z₀-z) + ∫ y in (0:ℝ)..R, ρ (u-y) * secondBranch z z₀ y := by
  rw [← (exponential_transfers u R z z₀ hρ hdρ hiρ hidρ hR hdR).2]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hR0] at hy
  rcases lt_or_eq_of_le hy.1 with hpos | rfl
  · simp [RelativeResolvent.logTest, positiveBranch, hpos]
  · simp [RelativeResolvent.logTest, positiveBranch]

end

#print axioms transfer_derivative
#print axioms first_transfer
#print axioms second_transfer
#print axioms positiveBranch_derivative
#print axioms firstBranch_derivative
#print axioms exponential_transfers
#print axioms logTest_second_transfer

end RHConnections.EndpointIBP
