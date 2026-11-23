import Verified
import FrozenWindowObstruction
import RankContrastTransfer

noncomputable section
open Set
namespace RHConnections.RankContrast
open LocalModeContrast

variable {ι κ : Type*}

theorem frozen_rank_window_obstruction
    (rho₀ : ℂ) (hrho₀ : rho₀≠0) (hrho₁ : rho₀≠1) (rho : κ → ℂ)
    (hsep : ∀ j,rho j≠rho₀) (hfinite : {j | |(rho j-rho₀).im|<2}.Finite)
    {C W : ℝ} (hC : 0≤C) (hW : 0<W)
    (hcount : ∀ (T : ℝ) (s : Finset κ), 1≤T →
      (∀ j∈s, |(rho j-rho₀).im|≤T) → (s.card:ℝ)≤C*Real.sqrt T) :
    ∃ R D : ℝ, 0<R ∧ 0≤D ∧ ∀ {A B rows : Finset ι} (hA : A.Nonempty) (hB : B.Nonempty)
      (ha : A⊆rows) (hb : B⊆rows)
      (a b : ι → ℝ) (gap L₀ m₀ : ℝ) (hg : 0<gap) (hL : 0<L₀) (hm : 0≤m₀)
      (roots : Finset κ) (mult : κ → ℂ) (hr : ∀ j∈roots,rho j≠0)
      (minLength error width centerCost rowCost : ℝ)
      (hmin : 0<minLength) (he : 0≤error) (hw : 0≤width) (hc : 0≤centerCost)
      (grid : ℝ → ι → ℝ) (value : ℝ → ι → ℂ) (scale : ℝ → ℝ),
      (∀ i, i∈A ∨ i∈B → 0<a i ∧ minLength≤b i-a i ∧
        a i∈Ioo (1-R) (1+R) ∧ b i∈Ioo (1-R) (1+R)) →
      (∀ i∈A,∀ j∈B,gap≤a i-a j ∧ gap≤b i-b j) →
      (∀ z∈Icc 0 W, ∃ c : ℂ, ‖c‖≤centerCost ∧
        Real.sqrt (∑ i∈rows,‖value z i-c*(grid z i:ℂ)‖^2)≤rowCost) →
      (∀ z∈Icc 0 W,∀ i, i∈A ∨ i∈B → |grid z i-scale z*(b i-a i)|≤width) →
      (∀ z∈Icc 0 W,
        let L := L₀*Real.exp z
        let frozen (i : ι) := (m₀:ℂ)*
            (zeroPrimitive rho₀ (L*b i)-zeroPrimitive rho₀ (L*a i))+
          ∑ j∈roots,mult j*(zeroPrimitive (rho j) (L*b i)-zeroPrimitive (rho j) (L*a i))
        ∀ i, i∈A ∨ i∈B → ‖frozen i-value z i‖≤error) →
      m₀*L₀^rho₀.re*gap*‖rho₀-1‖/2 ≤ D*
        (rowCost*((Real.sqrt (A.card:ℝ)*minLength)⁻¹+(Real.sqrt (B.card:ℝ)*minLength)⁻¹) +
          2*(error+centerCost*width)/minLength) := by
  obtain ⟨R,D,hR,hD,h⟩ := frozen_window_isolates_zero_contrast (ι := ι)
    rho₀ hrho₀ hrho₁ rho hsep hfinite hC hW hcount
  refine ⟨R,D,hR,hD,?_⟩
  intro A B rows hA hB ha hb a b gap L₀ m₀ hg hL hm roots mult hr L E V C₀ U hLmin hE hV hC₀
    grid value scale hloc hgap hcost hwidth herr
  apply h A B hA hB a b gap L₀ m₀ hg hL hm roots mult hr _
  · intro i hi
    have hh := hloc i hi
    exact ⟨⟨hh.1,by linarith [hh.2.1]⟩,hh.2.2⟩
  · exact hgap
  · intro z hz
    let F (i : ι) := (m₀:ℂ)*
      (zeroPrimitive rho₀ (L₀*Real.exp z*b i)-zeroPrimitive rho₀ (L₀*Real.exp z*a i))+
      ∑ j∈roots,mult j*(zeroPrimitive (rho j) (L₀*Real.exp z*b i)-zeroPrimitive (rho j) (L₀*Real.exp z*a i))
    change ‖contrast A B (fun i => b i-a i) F‖≤_
    obtain ⟨c,hc,hU⟩ := hcost z hz
    have hT := contrast_transfer_of_length_error hA hB ha hb
      (fun i => b i-a i) (grid z) (value z) F c (scale z) hLmin hE hV
      (fun i hi => (hloc i hi).2.1) (herr z hz) (hwidth z hz)
    refine hT.trans (add_le_add (mul_le_mul_of_nonneg_right hU (by positivity)) ?_)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hV)) (by norm_num))
      hLmin.le

end RHConnections.RankContrast
