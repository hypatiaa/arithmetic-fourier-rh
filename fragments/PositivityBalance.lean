import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace RHConnections.PositivityBalance

theorem main_lower_bound {ASK MAIN De : ℝ}
    (balance : ASK - MAIN = De) (positive : 0 ≤ ASK) : -De ≤ MAIN := by
  linarith

theorem one_sided_bound {ASK MAIN De base Gm gap : ℝ}
    (balance : ASK - MAIN = De) (positive : 0 ≤ ASK)
    (identification : MAIN = base - Gm) (gap_bound : De ≤ gap) :
    Gm ≤ base + gap := by
  linarith

#print axioms main_lower_bound
#print axioms one_sided_bound
end RHConnections.PositivityBalance
