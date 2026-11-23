import Verified

noncomputable section
open Filter
namespace RHConnections.PhaseWindow
open SpectralTail

theorem opposite_offsets_summable_of_sqrt_count {ι : Type*} (freq : ι → ℂ)
    (hfinite : {i | |(freq i).im|<2}.Finite)
    (C : ℝ) (hC : 0≤C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), 1≤T →
      (∀ i∈s, |(freq i).im|≤T) → (s.card:ℝ)≤C*Real.sqrt T) :
    Summable (fun i => oppositeOffset (freq i)) := by
  classical
  let f (i : ι) := if heightBin (freq i).im=0 then 0 else oppositeOffset (freq i)
  let S (j : ℕ) := {i : ι | heightBin (freq i).im=j}
  let u : ℝ := Real.sqrt 2
  let A := Real.pi*C*u
  let major (j : ℕ) := A*(u/2)^j
  have hu : 0≤u := Real.sqrt_nonneg _
  have hu2 : u<2 := by dsimp [u]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hA : 0≤A := by dsimp [A]; positivity [Real.pi_pos]
  have hp (j : ℕ) : Real.sqrt ((2:ℝ)^j)=u^j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,pow_succ,Real.sqrt_mul (by positivity),ih]
  have hf (i) : 0≤f i := by dsimp [f,oppositeOffset]; split <;> positivity [Real.pi_pos]
  have hpart (i : ι) : ∃! j, i∈S j :=
    ⟨heightBin (freq i).im,rfl,fun _ h => (show heightBin (freq i).im=_ from h).symm⟩
  have hbound (j : ℕ) (s : Finset (S j)) : (∑ i∈s,f i)≤major j := by
    by_cases hj : j=0
    · subst j
      have hh : ∀ i : S 0, f i=0 := fun i => ite_eq_left i.property
      simp only [hh,Finset.sum_const_zero]
      exact mul_nonneg hA (pow_nonneg (by positivity) _)
    let e : S j ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
    have hCard := hcount ((2:ℝ)^(j+1)) (s.map e) (one_le_pow₀ (by norm_num)) (by
      intro i hi
      obtain ⟨r,_,rfl⟩ := Finset.mem_map.mp hi
      have hu' := (heightBin_upper (freq r).im).le
      rw [show heightBin (freq r).im=j from r.property] at hu'
      exact hu')
    rw [Finset.card_map,hp] at hCard
    have hb (r : S j) : f r≤Real.pi/(2:ℝ)^j := by
      have hl := heightBin_lower (freq r).im (by rw [show heightBin (freq r).im=j from r.property]; exact hj)
      rw [show heightBin (freq r).im=j from r.property] at hl
      dsimp only [f]
      rw [show heightBin (freq r).im=j from r.property, ite_eq_right hj]
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hl
    calc
      _ ≤ ∑ _i∈s, Real.pi/(2:ℝ)^j := Finset.sum_le_sum (fun i _ => hb i)
      _ = (s.card:ℝ)*(Real.pi/(2:ℝ)^j) := by simp [nsmul_eq_mul]
      _ ≤ C*u^(j+1)*(Real.pi/(2:ℝ)^j) := mul_le_mul_of_nonneg_right hCard (by positivity [Real.pi_pos])
      _ = major j := by dsimp [major,A]; rw [div_pow,pow_succ]; ring
  have hg : Summable major :=
    (summable_geometric_of_lt_one (show 0≤u/2 by positivity) (by linarith : u/2<1)).mul_left A
  have hi (j) : Summable (fun r : S j => f r) := summable_of_sum_le (fun r => hf r) (hbound j)
  have hfs : Summable f :=
    (summable_partition hf hpart).2 ⟨hi,hg.of_nonneg_of_le
      (fun j => tsum_nonneg fun r => hf r) (fun j => le_of_tendsto (hi j).hasSum (Eventually.of_forall (hbound j)))⟩
  apply hfs.congr_cofinite
  have hOutside : ∀ᶠ i in Filter.cofinite, i∉{i | |(freq i).im|<2} :=
    hfinite.compl_mem_cofinite
  filter_upwards [hOutside] with i hi
  have hz : heightBin (freq i).im ≠ 0 := by
    intro hz
    have hu' := heightBin_upper (freq i).im
    rw [hz,zero_add,pow_one] at hu'
    exact hi hu'
  exact ite_eq_right hz

theorem uniform_window_isolation_of_sqrt_count {ι : Type*} (freq : ι → ℂ)
    (hzero : ∀ i,freq i≠0)
    (hfinite : {i | |(freq i).im|<2}.Finite)
    (C : ℝ) (hC : 0≤C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), 1≤T →
      (∀ i∈s, |(freq i).im|≤T) → (s.card:ℝ)≤C*Real.sqrt T) {W : ℝ} (hW : 0<W) :
    ∃ D : ℝ, 0≤D ∧ ∀ (s : Finset ι) (A : ι → ℂ) (target : ℂ) (B : ℝ),
      (∀ x ∈ Set.Icc 0 W, ‖target+∑ i∈s,A i*Complex.exp (freq i*(x:ℂ))‖≤B) →
      ‖target‖≤D*B := by
  classical
  exact uniform_window_isolation freq hzero
    ⟨hfinite.toFinset,fun i hi => hfinite.mem_toFinset.mpr (by simp [hi])⟩
    (opposite_offsets_summable_of_sqrt_count freq hfinite C hC hcount) hW

end RHConnections.PhaseWindow
