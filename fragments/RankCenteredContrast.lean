import Verified

noncomputable section
namespace RHConnections.RankContrast

variable {ι : Type*}

def mean (s : Finset ι) (z : ι → ℂ) : ℂ :=
  (∑ i∈s,z i)/(s.card:ℂ)

def contrast (A B : Finset ι) (length : ι → ℝ) (v : ι → ℂ) : ℂ :=
  mean A (fun i => v i/(length i:ℂ)) - mean B (fun i => v i/(length i:ℂ))

private theorem centered_mean {s : Finset ι} (hs : s.Nonempty) (length : ι → ℝ)
    (v : ι → ℂ) (c : ℂ) (hL : ∀ i∈s, 0<length i) :
    mean s (fun i => v i/(length i:ℂ))-c =
      mean s (fun i => (v i-c*(length i:ℂ))/(length i:ℂ)) := by
  unfold mean
  rw [sub_eq_iff_eq_add]
  have he : ∀ i∈s, (v i-c*(length i:ℂ))/(length i:ℂ) =
      v i/(length i:ℂ)-c := by
    intro i hi
    have hx := Complex.ofReal_ne_zero.mpr (hL i hi).ne'
    field_simp
  rw [Finset.sum_congr rfl he,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  have hc : (s.card:ℂ)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  field_simp
  <;> ring

private theorem mean_cost {s : Finset ι} (hs : s.Nonempty) {rows : Finset ι} (hsub : s⊆rows)
    (length : ι → ℝ) (v : ι → ℂ) (c : ℂ) {L : ℝ} (hL : 0<L)
    (hlen : ∀ i∈s, L≤length i) :
    ‖mean s (fun i => (v i-c*(length i:ℂ))/(length i:ℂ))‖ ≤
      (Real.sqrt (∑ i∈rows,‖v i-c*(length i:ℂ)‖^2)/(Real.sqrt (s.card:ℝ)*L)) := by
  let r (i : ι) := ‖v i-c*(length i:ℂ)‖
  have hc : (0:ℝ)<s.card := by exact_mod_cast hs.card_pos
  let E := ∑ i∈rows,r i^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hcauchy : (∑ i∈s,r i)^2 ≤ (s.card:ℝ)*E := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq s r (fun _ => (1:ℝ))
    have hv : (∑ i∈s,r i^2)≤E :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hv hc.le).trans_eq (by ring))
  have hsum : (∑ i∈s,r i) ≤ Real.sqrt (s.card:ℝ)*Real.sqrt E := by
    rw [← Real.sqrt_mul hc.le]
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr hcauchy
  have hterm (i) (hi : i∈s) :
      ‖(v i-c*(length i:ℂ))/(length i:ℂ)‖ ≤ r i/L := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hL.trans_le (hlen i hi))]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hL (hlen i hi)
  rw [mean,norm_div,Complex.norm_natCast]
  calc
    _ ≤ (∑ i∈s,r i/L)/(s.card:ℝ) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (∑ i∈s,r i)/(L*(s.card:ℝ)) := by rw [←Finset.sum_div,div_div]
    _ ≤ (Real.sqrt (s.card:ℝ)*Real.sqrt E)/(L*(s.card:ℝ)) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by
      change _ = Real.sqrt E/(Real.sqrt (s.card:ℝ)*L)
      field_simp
      rw [Real.sq_sqrt hc.le]
      ring

theorem centered_contrast_le {A B rows : Finset ι} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : A⊆rows) (hb : B⊆rows) (length : ι → ℝ) (v : ι → ℂ)
    (c : ℂ) {L : ℝ} (hL : 0<L)
    (hAl : ∀ i∈A, L≤length i) (hBl : ∀ i∈B, L≤length i) :
    ‖contrast A B length v‖ ≤
      Real.sqrt (∑ i∈rows,‖v i-c*(length i:ℂ)‖^2)*
        ((Real.sqrt (A.card:ℝ)*L)⁻¹+(Real.sqrt (B.card:ℝ)*L)⁻¹) := by
  unfold contrast
  rw [←sub_sub_sub_cancel_right _ _ c,centered_mean hA length v c
    (fun i hi => hL.trans_le (hAl i hi)),centered_mean hB length v c
    (fun i hi => hL.trans_le (hBl i hi))]
  exact ((norm_sub_le _ _).trans (add_le_add
    (mean_cost hA ha length v c hL hAl) (mean_cost hB hb length v c hL hBl))).trans_eq (by ring)

end RHConnections.RankContrast
