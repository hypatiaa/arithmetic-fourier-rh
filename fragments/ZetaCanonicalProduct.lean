import Verified
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.SummableUniformlyOn

open Filter Metric
noncomputable section
namespace RHConnections.CanonicalFactor
open SpectralTail

def zetaFactor (r : RepeatedZetaZero) (s : ℂ) : ℂ := genusOne (s/r.1.val)

def zetaCanonicalProduct (s : ℂ) : ℂ := ∏' r : RepeatedZetaZero, zetaFactor r s

theorem zetaFactor_differentiable (r : RepeatedZetaZero) : Differentiable ℂ (zetaFactor r) := by
  exact genusOne_differentiable.comp (differentiable_id.div_const _)

theorem zetaFactor_majorant_on_compact (K : Set ℂ) (hK : IsCompact K) :
    ∃ u : RepeatedZetaZero → ℝ, Summable u ∧
      ∀ r s, s ∈ K → ‖zetaFactor r s-1‖ ≤ u r := by
  obtain ⟨δ, hδ, hd⟩ := zeta_zero_norm_lower
  obtain ⟨L₀, hL₀⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let L := max L₀ 0
  let R := L/δ
  let A := max 3 ((1+R)*Real.exp R+1)
  let u := fun r : RepeatedZetaZero => (A * L^2) * (1/‖r.1.val‖^2)
  refine ⟨u, zeta_inverse_square_repeated.mul_left _, ?_⟩
  intro r s hs
  have hLs : ‖s‖ ≤ L := (hL₀ (Set.mem_image_of_mem _ hs)).trans (le_max_left _ _)
  have hq : 0 < ‖r.1.val‖ := hδ.trans_le (hd r.1)
  have hnorm : ‖s/r.1.val‖ ≤ R := by
    rw [norm_div]
    exact (div_le_div_of_nonneg_right hLs hq.le).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hδ (hd r.1))
  have hA : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 3).trans (le_max_left _ _)
  have hpow : ‖s‖^2 ≤ L^2 := pow_le_pow_left₀ (norm_nonneg _) hLs 2
  calc
    _ ≤ A * ‖s/r.1.val‖^2 := norm_genusOne_sub_one_le_on_disk hnorm
    _ ≤ A*(L^2/‖r.1.val‖^2) := by
      rw [norm_div, div_pow]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow (by positivity)) hA
    _ = u r := by dsimp [u]; ring

theorem zetaCanonicalProduct_locally_uniform :
    HasProdLocallyUniformlyOn zetaFactor zetaCanonicalProduct Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨u, hu, hb⟩ := zetaFactor_majorant_on_compact K hK
  have h := hu.hasProdUniformlyOn_one_add (f := fun r s => zetaFactor r s-1) hK
    (Filter.Eventually.of_forall hb)
    (fun r => ((zetaFactor_differentiable r).continuous.sub continuous_const).continuousOn)
  have he : (fun (i : RepeatedZetaZero) (x : ℂ) => 1 + (zetaFactor i x - 1)) = zetaFactor := by
    funext i x; ring
  have he' : (fun x : ℂ => ∏' i : RepeatedZetaZero, (1+(zetaFactor i x-1))) = zetaCanonicalProduct := by
    funext x
    unfold zetaCanonicalProduct
    exact tprod_congr fun i => by ring
  rw [he, he'] at h
  exact h

theorem zetaCanonicalProduct_entire :
    AnalyticOnNhd ℂ zetaCanonicalProduct Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  exact zetaCanonicalProduct_locally_uniform.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun i _ => (zetaFactor_differentiable i).differentiableOn)) isOpen_univ

end RHConnections.CanonicalFactor
