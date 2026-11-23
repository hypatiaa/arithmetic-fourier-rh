import Verified

noncomputable section
namespace RHConnections.SpectralTail

def MellinGrowthEnvelope (f : ℂ → ℂ) : Prop :=
  ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ R →
    ‖f s‖ ≤ C * Real.exp (D*R*Real.log R)

namespace MellinGrowthEnvelope

theorem const (c : ℂ) : MellinGrowthEnvelope (fun _ => c) := by
  refine ⟨‖c‖, 0, norm_nonneg _, le_rfl, ?_⟩
  intro R _ s _
  simp

theorem add {f g : ℂ → ℂ} (hf : MellinGrowthEnvelope f) (hg : MellinGrowthEnvelope g) :
    MellinGrowthEnvelope (fun s => f s + g s) := by
  obtain ⟨C,D,hC,hD,hf⟩ := hf
  obtain ⟨A,B,hA,hB,hg⟩ := hg
  refine ⟨C+A,max D B,add_nonneg hC hA,hD.trans (le_max_left _ _),?_⟩
  intro R hR s hs
  have hr : 0 ≤ R := by linarith
  have hl : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hmono {a b : ℝ} (h : a ≤ b) :
      Real.exp (a*R*Real.log R) ≤ Real.exp (b*R*Real.log R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hr) hl)
  calc
    _ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ C*Real.exp (D*R*Real.log R) + A*Real.exp (B*R*Real.log R) :=
      add_le_add (hf R hR s hs) (hg R hR s hs)
    _ ≤ C*Real.exp (max D B*R*Real.log R) + A*Real.exp (max D B*R*Real.log R) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmono (le_max_left _ _)) hC)
        (mul_le_mul_of_nonneg_left (hmono (le_max_right _ _)) hA)
    _ = _ := by ring

theorem mul {f g : ℂ → ℂ} (hf : MellinGrowthEnvelope f) (hg : MellinGrowthEnvelope g) :
    MellinGrowthEnvelope (fun s => f s * g s) := by
  obtain ⟨C,D,hC,hD,hf⟩ := hf
  obtain ⟨A,B,hA,hB,hg⟩ := hg
  refine ⟨C*A,D+B,mul_nonneg hC hA,add_nonneg hD hB,?_⟩
  intro R hR s hs
  change ‖f s * g s‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (C*Real.exp (D*R*Real.log R))*(A*Real.exp (B*R*Real.log R)) :=
      mul_le_mul (hf R hR s hs) (hg R hR s hs) (norm_nonneg _) (by positivity)
    _ = (C*A)*(Real.exp (D*R*Real.log R)*Real.exp (B*R*Real.log R)) := by ring
    _ = _ := by rw [← Real.exp_add, show D*R*Real.log R+B*R*Real.log R=(D+B)*R*Real.log R by ring]

theorem const_mul (c : ℂ) {f : ℂ → ℂ} (hf : MellinGrowthEnvelope f) :
    MellinGrowthEnvelope (fun s => c * f s) := (const c).mul hf

theorem finset_sum {ι : Type*} (t : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ t, MellinGrowthEnvelope (f i)) :
    MellinGrowthEnvelope (fun s => ∑ i ∈ t, f i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using const (0 : ℂ)
  | @insert i t hi ih =>
    have hi' := hf i (Finset.mem_insert_self i t)
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using hi'.add ht

theorem nat_cpow_neg {N : ℕ} (hN : 0 < N) :
    MellinGrowthEnvelope (fun s : ℂ => (N : ℂ)^(-s)) := by
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hN) : (1:ℝ) ≤ N)
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1,Real.log N / Real.log 2,zero_le_one,div_nonneg hL h₂.le,?_⟩
  intro R hR s hs
  change ‖(N : ℂ)^(-s)‖ ≤ _
  rw [Complex.norm_natCast_cpow_of_pos hN, Real.rpow_def_of_pos hN', one_mul]
  apply Real.exp_le_exp.mpr
  have hre : (-s).re ≤ R := (Complex.re_le_norm _).trans (by simpa only [norm_neg] using hs)
  have hlog : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  calc
    _ ≤ Real.log N * R := mul_le_mul_of_nonneg_left hre hL
    _ = (Real.log N/Real.log 2*R)*Real.log 2 := by field_simp [h₂.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

theorem translate {f : ℂ → ℂ} (hf : MellinGrowthEnvelope f) {b : ℂ} (hb : ‖b‖ ≤ 2) :
    MellinGrowthEnvelope (fun s => f (s+b)) := by
  obtain ⟨C,D,hC,hD,hf⟩ := hf
  refine ⟨C,4*D,hC,by positivity,?_⟩
  intro R hR s hs
  have hr : 0 < R := by linarith
  have hsr : ‖s+b‖ ≤ 2*R := (norm_add_le _ _).trans (by linarith)
  have hlog : Real.log (2*R) ≤ 2*Real.log R := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_le_log (by norm_num : 0 < (2:ℝ)) hR]
  apply (hf (2*R) (by linarith) (s+b) hsr).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ D*(2*R)*(2*Real.log R) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

end MellinGrowthEnvelope
end RHConnections.SpectralTail
