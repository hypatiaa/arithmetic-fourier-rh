import Verified
import ComplexCyclicPotential
import UniformGridRounding

noncomputable section
open Set
namespace RHConnections.BlockFourier
variable {J : ℕ} [NeZero J]

def shellBlockSignal (u : ℕ → ℝ) (F : ℝ → ℂ) (j : ZMod J) : ℂ :=
  F (u (j.val+1))-F (u j.val)

theorem shell_signal_at_nat (u : ℕ → ℝ) (F : ℝ → ℂ) {j : ℕ} (hj : j<J) :
    shellBlockSignal u F (j:ZMod J)=F (u (j+1))-F (u j) := by
  simp only [shellBlockSignal,ZMod.val_natCast_of_lt hj]

theorem shell_interval_potential (u : ℕ → ℝ) (F : ℝ → ℂ) (b len : ℕ)
    (hle : b+len≤J) :
    complexIntervalSum (shellBlockSignal u F) (b:ZMod J) len =
      F (u (b+len))-F (u b) := by
  induction len with
  | zero => simp [complexIntervalSum]
  | succ len ih =>
    rw [complexIntervalSum,Finset.sum_range_succ,←complexIntervalSum]
    rw [ih (by omega),←Nat.cast_add,shell_signal_at_nat u F (by omega)]
    rw [show b+(len+1)=b+len+1 by omega]
    ring

theorem real_active_length_monotone (u : ℕ → ℝ) :
    Monotone (realActiveLength J u) := by
  intro a b hab
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hj,h⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hj,h.trans hab⟩

theorem frozen_shell_row_error (u : ℕ → ℝ) (hu : Monotone u)
    {H D B a b : ℝ} (hH : 0≤H) (hD : 0≤D) (hB : 0≤B)
    (ha : a∈Icc (u 0) (u J)) (hb : b∈Icc (u 0) (u J)) (hab : a≤b)
    (hwidth : ∀ j<J,u (j+1)-u j≤H)
    (F G : ℝ → ℂ)
    (hF : ∀ x∈Icc (u 0) (u J),∀ y∈Icc (u 0) (u J),‖F x-F y‖≤D*|x-y|)
    (hG : ∀ x∈Icc (u 0) (u J),∀ y∈Icc (u 0) (u J),‖G x-G y‖≤B)
    (R : ℕ) (hR : 0<R) (hRJ : R≤J) :
    let start := realActiveLength J u a
    let len := realActiveLength J u b-start
    ‖complexIntervalSum
        (smoothComplexPositive (smoothingKernel R) (shellBlockSignal u (fun x => F x+G x)))
        (start:ZMod J) len - (F b-F a)‖ ≤
      12*D*H*(J:ℝ)/(R:ℝ)+2*B+2*D*H := by
  let ka := realActiveLength J u a
  let kb := realActiveLength J u b
  let len := kb-ka
  have hk : ka≤kb := real_active_length_monotone u hab
  have hkb : kb≤J := (real_grid_rounding J u hu hH hb.1 hb.2 hwidth).1
  have hka : ka≤J := hk.trans hkb
  have hlen : len≤J := (Nat.sub_le ..).trans hkb
  have hsum : ka+len=kb := Nat.add_sub_of_le hk
  have hSite (x : ZMod J) : ‖shellBlockSignal u F x‖≤D*H := by
    have hx := ZMod.val_lt x
    dsimp [shellBlockSignal]
    refine (hF _ ⟨hu (Nat.zero_le _),hu (Nat.succ_le_of_lt hx)⟩ _ ⟨hu (Nat.zero_le _),hu hx.le⟩).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr (hu (Nat.le_succ _)))]
    exact mul_le_mul_of_nonneg_left (hwidth _ hx) hD
  have hsmoothF := complex_interval_jackson_bound (shellBlockSignal u F) (D*H) hSite R hR hRJ
    (ka:ZMod J) len
  have hsiteG (x : ZMod J) (n : ℕ) (hn : n≤J) :
      ‖complexIntervalSum (shellBlockSignal u G) x n‖≤2*B := by
    apply complex_cyclic_potential_bound (shellBlockSignal u G) (fun j => G (u j))
      (fun j hj => shell_signal_at_nat u G hj) hB _ x n hn
    intro j hj k hk'
    exact hG _ ⟨hu (Nat.zero_le _),hu hj⟩ _ ⟨hu (Nat.zero_le _),hu hk'⟩
  have hsmoothG := complex_cyclic_bound_preserved (shellBlockSignal u G)
    (smoothingKernel R) (smoothing_kernel_nonneg R) (smoothing_kernel_mass hR)
    hsiteG (ka:ZMod J) len hlen
  have hRound := real_grid_interval_discretization J u hu hH hD ha hb hwidth F hF
  let dF := shellBlockSignal (J := J) u F
  let dG := shellBlockSignal (J := J) u G
  let lowF := smoothComplexPositive (smoothingKernel R) dF
  let lowG := smoothComplexPositive (smoothingKernel R) dG
  have hsumFG : smoothComplexPositive (smoothingKernel R) (shellBlockSignal u (fun x => F x+G x)) =
      lowF+lowG := by
    ext x
    change smoothComplexPositive _ _ x = lowF x+lowG x
    simp only [lowF,lowG,dF,dG,shellBlockSignal,smoothComplexPositive,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let I (d : ZMod J → ℂ) := complexIntervalSum d (ka:ZMod J) len
  have hIadd (d e : ZMod J → ℂ) : I (d+e)=I d+I e := by
    simp only [I,complexIntervalSum,Pi.add_apply,Finset.sum_add_distrib]
  have hIsub (d e : ZMod J → ℂ) : I (d-e)=I d-I e := by
    simp only [I,complexIntervalSum,Pi.sub_apply,Finset.sum_sub_distrib]
  have hgrid : I dF = F (u kb)-F (u ka) := by
    unfold I dF
    rw [shell_interval_potential u F ka len (by rwa [hsum]),hsum]
  change ‖I (smoothComplexPositive (smoothingKernel R) (shellBlockSignal u (fun x => F x+G x))) -
    (F b-F a)‖≤_
  rw [hsumFG,hIadd,show I lowF+I lowG-(F b-F a) =
    -(I dF-I lowF)+I lowG+(I dF-(F b-F a)) by ring]
  have h1 : ‖-(I dF-I lowF)‖≤12*(D*H)*(J:ℝ)/(R:ℝ) := by
    rw [norm_neg,←hIsub]
    exact hsmoothF
  have h2 : ‖I lowG‖≤2*B := hsmoothG
  have h3 : ‖I dF-(F b-F a)‖≤2*D*H := by rw [hgrid]; exact hRound
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)).trans_eq (by ring)

end RHConnections.BlockFourier
