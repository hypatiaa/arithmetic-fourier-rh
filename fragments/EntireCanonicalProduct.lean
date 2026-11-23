import Verified
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.SummableUniformlyOn

open Filter Metric
noncomputable section
namespace RHConnections.EntireCanonicalProduct
open CanonicalFactor SpectralTail

abbrev ZeroOf (F : ℂ → ℂ) := {s : ℂ // F s = 0}
abbrev RepeatedZeroOf (F : ℂ → ℂ) := Σ r : ZeroOf F, Fin (analyticOrderNatAt F r.val)

structure Data where
  F : ℂ → ℂ
  entire : AnalyticOnNhd ℂ F Set.univ
  at_zero : F 0 = 1
  square_summable : Summable (fun r : RepeatedZeroOf F => 1 / ‖r.1.val‖^2)

end RHConnections.EntireCanonicalProduct

namespace RHConnections.EntireCanonicalProduct.Data
open CanonicalFactor SpectralTail
variable (D : Data)

abbrev Zero := ZeroOf D.F
abbrev RepeatedZero := RepeatedZeroOf D.F

theorem zero_norm_lower : ∃ δ : ℝ, 0 < δ ∧ ∀ r : D.Zero, δ ≤ ‖r.val‖ := by
  have hn : D.F 0 ≠ 0 := by rw [D.at_zero]; exact one_ne_zero
  have hnear := (D.entire 0 (Set.mem_univ _)).continuousAt.eventually_ne hn
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ,hδ, fun r => le_of_not_gt fun hr => ?_⟩
  exact hh (show dist r.val (0 : ℂ) < δ by simpa only [dist_zero_right] using hr) r.property

theorem zero_finite_order (r : D.Zero) :
    AnalyticAt ℂ D.F r.val ∧ analyticOrderAt D.F r.val ≠ ⊤ := by
  have hn : D.F 0 ≠ 0 := by rw [D.at_zero]; exact one_ne_zero
  have h₀ : analyticOrderAt D.F 0 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hn)]
    exact WithTop.zero_ne_top
  exact ⟨D.entire _ (Set.mem_univ _), D.entire.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) h₀⟩

def factor (r : D.RepeatedZero) (s : ℂ) : ℂ := genusOne (s/r.1.val)

def product (s : ℂ) : ℂ := ∏' r : D.RepeatedZero, D.factor r s

theorem factor_differentiable (r : D.RepeatedZero) : Differentiable ℂ (D.factor r) := by
  exact genusOne_differentiable.comp (differentiable_id.div_const _)

theorem factor_majorant_on_compact (K : Set ℂ) (hK : IsCompact K) :
    ∃ u : D.RepeatedZero → ℝ, Summable u ∧
      ∀ r s, s ∈ K → ‖D.factor r s-1‖ ≤ u r := by
  obtain ⟨δ, hδ, hd⟩ := D.zero_norm_lower
  obtain ⟨L₀, hL₀⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let L := max L₀ 0
  let R := L/δ
  let A := max 3 ((1+R)*Real.exp R+1)
  let u := fun r : D.RepeatedZero => (A * L^2) * (1/‖r.1.val‖^2)
  refine ⟨u, D.square_summable.mul_left _, ?_⟩
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

theorem product_locally_uniform :
    HasProdLocallyUniformlyOn D.factor D.product Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨u, hu, hb⟩ := D.factor_majorant_on_compact K hK
  have h := hu.hasProdUniformlyOn_one_add (f := fun r s => D.factor r s-1) hK
    (Filter.Eventually.of_forall hb)
    (fun r => ((D.factor_differentiable r).continuous.sub continuous_const).continuousOn)
  have he : (fun (i : D.RepeatedZero) (x : ℂ) => 1 + (D.factor i x - 1)) = D.factor := by
    funext i x; ring
  have he' : (fun x : ℂ => ∏' i : D.RepeatedZero, (1+(D.factor i x-1))) = D.product := by
    funext x
    unfold product
    exact tprod_congr fun i => by ring
  rw [he, he'] at h
  exact h

theorem product_entire :
    AnalyticOnNhd ℂ D.product Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  exact D.product_locally_uniform.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun i _ => (D.factor_differentiable i).differentiableOn)) isOpen_univ

theorem factor_eq_zero_iff (r : D.RepeatedZero) (s : ℂ) :
    D.factor r s = 0 ↔ s = r.1.val := by
  obtain ⟨δ, hδ, hd⟩ := D.zero_norm_lower
  have hn : r.1.val ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hd r.1))
  unfold factor genusOne
  rw [mul_eq_zero]
  simp only [Complex.exp_ne_zero, or_false, sub_eq_zero]
  constructor
  · intro h
    have h' := (div_eq_iff hn).mp h.symm
    simpa using h'
  · intro h
    rw [h, div_self hn]

theorem product_ne_zero {s : ℂ} (h : ∀ r : D.Zero, s ≠ r.val) :
    D.product s ≠ 0 := by
  obtain ⟨u, hu, hb⟩ := D.factor_majorant_on_compact {s} isCompact_singleton
  have hm : Summable (fun r => ‖D.factor r s-1‖) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => hb r s (Set.mem_singleton s))
  have he (r : D.RepeatedZero) : 1+(D.factor r s-1) = D.factor r s := by ring
  have hz : ∀ r : D.RepeatedZero, 1+(D.factor r s-1) ≠ 0 := by
    intro r
    rw [he]
    exact fun hr => h r.1 ((D.factor_eq_zero_iff r s).mp hr)
  have hh := tprod_one_add_ne_zero_of_summable hz hm
  simpa only [he, product] using hh

theorem product_zero (r : D.Zero) : D.product r.val = 0 := by
  obtain ⟨ha, hf⟩ := D.zero_finite_order r
  let i : D.RepeatedZero := ⟨r, ⟨0, zero_order_positive r.property ha hf⟩⟩
  exact tprod_of_exists_eq_zero
    ⟨i, (D.factor_eq_zero_iff i r.val).mpr rfl⟩

def subproduct (A : Set D.RepeatedZero) (s : ℂ) : ℂ :=
  ∏' i : A, D.factor i.val s

theorem subproduct_locally_uniform (A : Set D.RepeatedZero) :
    HasProdLocallyUniformlyOn (fun (i : A) => D.factor i.val) (D.subproduct A) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨u, hu, hb⟩ := D.factor_majorant_on_compact K hK
  have h := (hu.subtype A).hasProdUniformlyOn_one_add
    (f := fun (i : A) s => D.factor i.val s-1) hK
    (.of_forall fun i s hs => hb i.val s hs)
    (fun i => ((D.factor_differentiable i.val).continuous.sub continuous_const).continuousOn)
  have he : (fun (i : A) (x : ℂ) => 1+(D.factor i.val x-1)) =
      (fun i : A => D.factor i.val) := by funext i x; ring
  have he' : (fun x : ℂ => ∏' i : A, (1+(D.factor i.val x-1))) = D.subproduct A := by
    funext x
    unfold subproduct
    exact tprod_congr fun i => by ring
  rw [he, he'] at h
  exact h

theorem subproduct_entire (A : Set D.RepeatedZero) :
    AnalyticOnNhd ℂ (D.subproduct A) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  exact (D.subproduct_locally_uniform A).differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun (i : A) _ => (D.factor_differentiable i.val).differentiableOn))
    isOpen_univ

def fiber (r : D.Zero) : Set D.RepeatedZero := {i | i.1 = r}

private def fiberEquiv (r : D.Zero) :
    Fin (analyticOrderNatAt D.F r.val) ≃ D.fiber r where
  toFun j := ⟨⟨r,j⟩, rfl⟩
  invFun i := (show i.val.1 = r from i.property) ▸ i.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨t,j⟩,h⟩
    change t = r at h
    subst t
    rfl

theorem product_split (r : D.Zero) (s : ℂ) :
    D.product s = genusOne (s/r.val) ^ analyticOrderNatAt D.F r.val *
      D.subproduct (D.fiber r)ᶜ s := by
  have h (A : Set D.RepeatedZero) :
      Multipliable ((fun i => D.factor i s) ∘ ((↑) : A → D.RepeatedZero)) :=
    ((D.subproduct_locally_uniform A).hasProd (Set.mem_univ s)).multipliable
  have he := (D.fiberEquiv r).tprod_eq (fun i : D.fiber r => D.factor i.val s)
  change (∏' _ : Fin (analyticOrderNatAt D.F r.val), genusOne (s/r.val)) = _ at he
  rw [tprod_fintype] at he
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  exact (Multipliable.tprod_mul_tprod_compl (h (D.fiber r)) (h (D.fiber r)ᶜ)).symm.trans
    (congrArg (fun a => a*D.subproduct (D.fiber r)ᶜ s) he.symm)

theorem subproduct_compl_ne_zero (r : D.Zero) :
    D.subproduct (D.fiber r)ᶜ r.val ≠ 0 := by
  obtain ⟨u, hu, hb⟩ := D.factor_majorant_on_compact {r.val} isCompact_singleton
  let A := (D.fiber r)ᶜ
  have hm : Summable (fun i : A => ‖D.factor i.val r.val-1‖) :=
    (hu.subtype A).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i.val _ (Set.mem_singleton _))
  have he (a : ℂ) : 1+(a-1)=a := by ring
  have hz (i : A) : 1+(D.factor i.val r.val-1) ≠ 0 := by
    rw [he]
    intro h
    exact i.property (Subtype.ext ((D.factor_eq_zero_iff i.val r.val).mp h).symm)
  simpa only [he, subproduct] using tprod_one_add_ne_zero_of_summable hz hm

theorem product_order (r : D.Zero) :
    analyticOrderAt D.product r.val = analyticOrderAt D.F r.val := by
  obtain ⟨δ,hδ,hd⟩ := D.zero_norm_lower
  have hr : r.val ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hd r))
  let m := analyticOrderNatAt D.F r.val
  let E := fun s : ℂ => -(r.val)⁻¹ * Complex.exp (s/r.val)
  have ha : AnalyticAt ℂ E r.val := by dsimp [E]; fun_prop
  have hn : E r.val ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hr)) (Complex.exp_ne_zero _)
  rw [← Nat.cast_analyticOrderNatAt (D.zero_finite_order r).2]
  apply (D.product_entire _ (Set.mem_univ _)).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun s => E s ^ m * D.subproduct (D.fiber r)ᶜ s,
    (ha.pow m).mul (D.subproduct_entire _ _ (Set.mem_univ _)),
    mul_ne_zero (pow_ne_zero _ hn) (D.subproduct_compl_ne_zero r), .of_forall ?_⟩
  intro s
  have he : genusOne (s/r.val) = (s-r.val)*E s := by
    unfold genusOne E
    field_simp [hr] <;> ring
  rw [D.product_split, he, mul_pow, smul_eq_mul]
  change (s-r.val)^m * E s^m * _ = _
  ring

theorem product_eq_zero_iff (s : ℂ) : D.product s = 0 ↔ D.F s = 0 := by
  refine ⟨fun hp => by
    by_contra h
    exact D.product_ne_zero (s := s) (fun r he => h (he.symm ▸ r.property)) hp,
    fun h => D.product_zero ⟨s,h⟩⟩

theorem product_order_everywhere (s : ℂ) :
    analyticOrderAt D.product s = analyticOrderAt D.F s := by
  by_cases h : D.F s = 0
  · exact D.product_order ⟨s,h⟩
  · have hp : D.product s ≠ 0 := fun hz => h ((D.product_eq_zero_iff s).mp hz)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hp), analyticOrderAt_eq_zero.mpr (Or.inr h)]

theorem product_at_zero : D.product 0 = 1 := by
  simp [product, factor, genusOne]

end RHConnections.EntireCanonicalProduct.Data
