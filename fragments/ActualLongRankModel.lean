import Verified
import ZetaRightDensity
import FiniteZeroPotential
import RealDyadicMesh
import BlockComplexTransfer
import FrozenShellGridError

noncomputable section
open Filter Set
namespace RHConnections.LongRankPhase
open RHConnections.RankPairing RHConnections.BlockFourier
open RHConnections.PhaseWindow RHConnections.LocalModeContrast

inductive RankRowKind where
  | pair
  | positive
  | negative
  deriving DecidableEq

abbrev RankRow := RankRowKind × ℕ

def rankRows (N : ℕ) : Finset RankRow :=
  let P := positivePositions N
  let V := negativePositions N
  let k := min P.card V.card
  (({RankRowKind.pair} : Finset RankRowKind) ×ˢ Finset.range k) ∪
    (({RankRowKind.positive} : Finset RankRowKind) ×ˢ Finset.Ico k P.card) ∪
    (({RankRowKind.negative} : Finset RankRowKind) ×ˢ Finset.Ico k V.card)

def rowWeight (r : RankRow) : ℝ := if r.1=RankRowKind.pair then 1/2 else 1

def rowEndpoints (N : ℕ) (r : RankRow) : ℕ × ℕ :=
  let p := indexAt (positivePositions N) r.2
  let n := indexAt (negativePositions N) r.2
  match r.1 with
  | .pair => (min p n,max p n)
  | .positive => (p,N+1)
  | .negative => (n,N+1)

def rightHeightSet (T : ℝ) : Set RightZero := {r | |(rightValue r).im|<T}

theorem right_height_finite (T : ℝ) : (rightHeightSet T).Finite :=
  (finite_right_zeros_of_bounded_height T).subset (fun r h => show |(rightValue r).im|≤T from (show |(rightValue r).im|<T from h).le)

def rightHeightFinset (T : ℝ) : Finset RightZero := (right_height_finite T).toFinset

def zeroMultiplicity (r : RightZero) : ℝ :=
  (analyticOrderNatAt riemannZeta (rightValue r):ℝ)

def rightPotential (Q : ℝ) : ℝ → ℂ :=
  finiteZeroPotential (rightHeightFinset (Q^(1/8:ℝ))) rightValue zeroMultiplicity

def rowStartLength (X Q : ℝ) (r : RankRow) : ℕ × ℕ :=
  let limits := rowEndpoints ⌊X/Q⌋₊ r
  let J := realDyadicMeshCount Q
  let u := realDyadicMeshPoint Q
  let start := realActiveLength J u (X/(limits.2:ℝ))
  let stop := realActiveLength J u (X/(limits.1:ℝ))
  (start,stop-start)

def longRowValue (X Q : ℝ) (r : RankRow) : ℂ :=
  let j := realDyadicMeshCount Q
  let R := realDyadicMeshRadius Q
  let limits := rowStartLength X Q r
  if hj : 0<j then
    letI : NeZero j := ⟨hj.ne'⟩
    if Q^(-(1/8:ℝ)) < (limits.2:ℝ)/(j:ℝ) then
      let d : ZMod j → ℂ := shellBlockSignal (realDyadicMeshPoint Q) (rightPotential Q)
      complexIntervalSum (smoothComplexPositive (smoothingKernel R) d) (limits.1:ZMod j) limits.2
    else 0
  else 0

def longRowCost (X Q : ℝ) (c : ℂ) : ℝ :=
  Real.sqrt (∑ r∈rankRows ⌊X/Q⌋₊,rowWeight r *
    ‖longRowValue X Q r-c*((rowStartLength X Q r).2:ℂ)‖^2)

def UniformLongRowPower (eta delta : ℝ) : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∀ᶠ X : ℝ in atTop, ∃ c : ℂ,
    longRowCost X (X^eta) c ≤ C*Real.sqrt (⌊X/(X^eta)⌋₊:ℝ)*(X^eta)^(1-delta)

end RHConnections.LongRankPhase
