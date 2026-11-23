import Verified

noncomputable section

namespace RHConnections.PhaseWindow

structure Shift where
  weight : ℂ
  offset : ℝ

noncomputable def applyWindow (f : ℝ → ℂ) (z : ℝ) : List Shift → ℂ
  | [] => f z
  | e :: tail => (1-e.weight)*applyWindow f z tail +
      e.weight*applyWindow f (z+e.offset) tail

private def applyWindowFold (f : ℝ → ℂ) (z : ℝ) (steps : List Shift) : ℂ :=
  steps.foldr (fun e g x => (1-e.weight)*g x + e.weight*g (x+e.offset)) f z

private theorem applyWindowFold_cons (f : ℝ → ℂ) (z : ℝ) (e : Shift) (tail : List Shift) :
    applyWindowFold f z (e :: tail) =
      (1-e.weight)*applyWindowFold f z tail + e.weight*applyWindowFold f (z+e.offset) tail := rfl

@[csimp] private theorem applyWindow_eq_fold : @applyWindow = @applyWindowFold := by
  funext f z steps
  induction steps generalizing z with
  | nil => rfl
  | cons e tail ih => simp only [applyWindow, applyWindowFold_cons, ih]

def windowCost (steps : List Shift) : ℝ :=
  (steps.map fun e => ‖1-e.weight‖+‖e.weight‖).prod

def windowWidth (steps : List Shift) : ℝ :=
  (steps.map Shift.offset).sum

def shiftFactor (freq : ℂ) (e : Shift) : ℂ :=
  1-e.weight+e.weight*Complex.exp (freq*(e.offset:ℂ))

theorem apply_window_add (f g : ℝ → ℂ) (steps : List Shift) (z : ℝ) :
    applyWindow (fun x => f x+g x) z steps =
      applyWindow f z steps+applyWindow g z steps := by
  induction steps generalizing z with
  | nil => rfl
  | cons e tail ih =>
    simp only [applyWindow,ih]
    ring

theorem apply_window_mul_const (a : ℂ) (f : ℝ → ℂ) (steps : List Shift) (z : ℝ) :
    applyWindow (fun x => a*f x) z steps = a*applyWindow f z steps := by
  induction steps generalizing z with
  | nil => rfl
  | cons e tail ih =>
    simp only [applyWindow,ih]
    ring

theorem apply_window_exponential (freq : ℂ) (steps : List Shift) (z : ℝ) :
    applyWindow (fun x => Complex.exp (freq*(x:ℂ))) z steps =
      Complex.exp (freq*(z:ℂ))*(steps.map (shiftFactor freq)).prod := by
  induction steps generalizing z with
  | nil => simp [applyWindow]
  | cons e tail ih =>
    simp only [applyWindow,ih,List.map_cons,List.prod_cons,shiftFactor,Complex.ofReal_add,
      mul_add,Complex.exp_add]
    ring

theorem apply_window_cost (f : ℝ → ℂ) (steps : List Shift) (z B : ℝ)
    (hpos : ∀ e ∈ steps, 0≤e.offset)
    (hf : ∀ x, z≤x → x≤z+windowWidth steps → ‖f x‖≤B) :
    ‖applyWindow f z steps‖ ≤ B*windowCost steps := by
  induction steps generalizing z with
  | nil => simpa [applyWindow,windowCost] using hf z le_rfl (by simp [windowWidth])
  | cons e tail ih =>
    have he := hpos e (List.mem_cons_self ..)
    have hp (v) (hv : v ∈ tail) := hpos v (List.mem_cons_of_mem _ hv)
    have hwidth : windowWidth (e::tail)=e.offset+windowWidth tail := rfl
    have h₀ := ih z hp (fun x hl hr => hf x hl (by rw [hwidth]; linarith))
    have h₁ := ih (z+e.offset) hp (fun x hl hr => hf x (by linarith) (by rw [hwidth]; linarith))
    calc
      _ ≤ ‖(1-e.weight)*applyWindow f z tail‖+
            ‖e.weight*applyWindow f (z+e.offset) tail‖ := norm_add_le _ _
      _ ≤ ‖1-e.weight‖*(B*windowCost tail)+‖e.weight‖*(B*windowCost tail) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h₀ (norm_nonneg _))
          (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
      _ = _ := by simp only [windowCost,List.map_cons,List.prod_cons]; ring

theorem window_kills_mode {freq : ℂ} {steps : List Shift} {e : Shift}
    (he : e ∈ steps) (hkill : shiftFactor freq e=0) (z : ℝ) :
    applyWindow (fun x => Complex.exp (freq*(x:ℂ))) z steps=0 := by
  rw [apply_window_exponential]
  rw [List.prod_eq_zero (List.mem_map.mpr ⟨e,he,hkill⟩),mul_zero]

theorem window_keeps_constants (a : ℂ) (steps : List Shift) (z : ℝ) :
    applyWindow (fun _ => a) z steps = a := by
  induction steps generalizing z with
  | nil => rfl
  | cons e tail ih => simp only [applyWindow,ih]; ring

theorem window_isolates_exponential_sum {ι : Type*} (s : Finset ι)
    (A freq : ι → ℂ) (j : ι) (hj : j ∈ s) (hfreq : freq j=0) (steps : List Shift) (z : ℝ)
    (hk : ∀ i ∈ s, i≠j → ∃ e ∈ steps, shiftFactor (freq i) e=0) :
    applyWindow (fun x => ∑ i ∈ s, A i*Complex.exp (freq i*(x:ℂ))) z steps = A j := by
  classical
  have hsum (t : Finset ι) :
      applyWindow (fun x => ∑ i ∈ t, A i*Complex.exp (freq i*(x:ℂ))) z steps =
        ∑ i ∈ t, A i*applyWindow (fun x => Complex.exp (freq i*(x:ℂ))) z steps := by
    induction t using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,window_keeps_constants]
    | insert i t hi ih =>
      simp only [Finset.sum_insert hi,apply_window_add,apply_window_mul_const,ih]
  rw [hsum]
  rw [Finset.sum_eq_single_of_mem j hj]
  · simp only [hfreq,zero_mul,Complex.exp_zero,window_keeps_constants,mul_one]
  · intro i hi hij
    obtain ⟨e,he,hzero⟩ := hk i hi hij
    rw [window_kills_mode he hzero,mul_zero]

end RHConnections.PhaseWindow
