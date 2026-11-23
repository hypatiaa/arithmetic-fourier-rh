import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

open Filter
open scoped Topology
noncomputable section
namespace RHConnections.ZetaEulerNearOne

private theorem term_bound {s : ℂ} (hs : 3 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (1 : ℕ → ℂ) s (n+2)‖ ≤
      (1/2 : ℝ) * (1/((n:ℝ)+1) - 1/((n:ℝ)+2)) := by
  let a : ℝ := (n:ℝ)+2
  have ha : 2 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : 0 < a := by linarith
  have hpow : a^3 ≤ a^s.re := by
    calc
      a^3 = a^(3:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have ht : ‖LSeries.term (1 : ℕ → ℂ) s (n+2)‖ = 1/a^s.re := by
    rw [LSeries.term_of_ne_zero (show n+2 ≠ 0 by omega), norm_div]
    change ‖(1:ℂ)‖ / ‖((n+2 : ℕ) : ℂ)^s‖ = _
    rw [show ((n+2 : ℕ) : ℂ) = (a:ℂ) by simp [a], Complex.norm_cpow_eq_rpow_re_of_pos hp,
      norm_one]
  rw [ht]
  refine (one_div_le_one_div_of_le (show 0 < a^3 by positivity) hpow).trans ?_
  have hh : 0 < (n:ℝ)+1 := by positivity
  dsimp [a]
  field_simp
  <;> nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n:ℝ), pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]

theorem norm_zeta_sub_one_le_half {s : ℂ} (hs : 3 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 1/2 := by
  let f := LSeries.term (1 : ℕ → ℂ) s
  have h₁ : 1 < s.re := by linarith
  have hsumm : HasSum f (riemannZeta s) := by
    rw [← LSeries_one_eq_riemannZeta h₁]
    exact (show Summable f from LSeriesSummable_one_iff.mpr h₁).hasSum
  have hbound (n : ℕ) :
      ‖(∑ k ∈ Finset.range (n+2), f k) - 1‖ ≤ (1/2 : ℝ)*(1-1/((n:ℝ)+1)) := by
    induction n with
    | zero => norm_num [f, Finset.sum_range_succ, LSeries.term]
    | succ n ih =>
      rw [show n.succ+2 = (n+2)+1 by omega, Finset.sum_range_succ]
      rw [show (∑ k ∈ Finset.range (n+2), f k) + f (n+2) - 1 =
        ((∑ k ∈ Finset.range (n+2), f k)-1) + f (n+2) by ring]
      have he : ((n.succ : ℕ) : ℝ)+1 = (n:ℝ)+2 := by push_cast; ring
      rw [he]
      refine (norm_add_le _ _).trans ((add_le_add ih (term_bound hs n)).trans_eq ?_)
      ring
  apply le_of_tendsto ((hsumm.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)).sub_const (1:ℂ)).norm
  exact Eventually.of_forall fun n => (hbound n).trans (by
    have h : 0 ≤ 1/((n:ℝ)+1) := by positivity
    linarith)

theorem zeta_right_bounds {s : ℂ} (hs : 3 ≤ s.re) :
    (1/2 : ℝ) ≤ ‖riemannZeta s‖ ∧ ‖riemannZeta s‖ ≤ 3/2 ∧ (1/2 : ℝ) ≤ (riemannZeta s).re := by
  have h := norm_zeta_sub_one_le_half hs
  have hrev := norm_sub_norm_le (1:ℂ) (riemannZeta s)
  rw [norm_sub_rev, norm_one] at hrev
  have hup := norm_add_le (riemannZeta s - 1) (1:ℂ)
  rw [sub_add_cancel, norm_one] at hup
  have hr := Complex.abs_re_le_norm (riemannZeta s - 1)
  rw [Complex.sub_re, Complex.one_re] at hr
  exact ⟨by linarith, by linarith, by linarith [neg_le_abs ((riemannZeta s).re-1)]⟩

end RHConnections.ZetaEulerNearOne
