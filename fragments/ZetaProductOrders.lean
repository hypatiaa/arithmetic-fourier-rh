import Verified

noncomputable section
namespace RHConnections.CanonicalFactor
open SpectralTail Filter

def zetaSubproduct (A : Set RepeatedZetaZero) (s : ℂ) : ℂ :=
  ∏' i : A, zetaFactor i.val s

theorem zetaSubproduct_locally_uniform (A : Set RepeatedZetaZero) :
    HasProdLocallyUniformlyOn (fun (i : A) => zetaFactor i.val) (zetaSubproduct A) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨u, hu, hb⟩ := zetaFactor_majorant_on_compact K hK
  have h := (hu.subtype A).hasProdUniformlyOn_one_add
    (f := fun (i : A) s => zetaFactor i.val s-1) hK
    (.of_forall fun i s hs => hb i.val s hs)
    (fun i => ((zetaFactor_differentiable i.val).continuous.sub continuous_const).continuousOn)
  have he : (fun (i : A) (x : ℂ) => 1+(zetaFactor i.val x-1)) =
      (fun i : A => zetaFactor i.val) := by funext i x; ring
  have he' : (fun x : ℂ => ∏' i : A, (1+(zetaFactor i.val x-1))) = zetaSubproduct A := by
    funext x
    unfold zetaSubproduct
    exact tprod_congr fun i => by ring
  rw [he, he'] at h
  exact h

theorem zetaSubproduct_entire (A : Set RepeatedZetaZero) :
    AnalyticOnNhd ℂ (zetaSubproduct A) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  exact (zetaSubproduct_locally_uniform A).differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun (i : A) _ => (zetaFactor_differentiable i.val).differentiableOn))
    isOpen_univ

def zeroFiber (r : NontrivialZetaZero) : Set RepeatedZetaZero := {i | i.1 = r}

private def zeroFiberEquiv (r : NontrivialZetaZero) :
    Fin (analyticOrderNatAt riemannZeta r.val) ≃ zeroFiber r where
  toFun j := ⟨⟨r,j⟩, rfl⟩
  invFun i := (show i.val.1 = r from i.property) ▸ i.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨t,j⟩,h⟩
    change t = r at h
    subst t
    rfl

theorem zetaCanonicalProduct_split (r : NontrivialZetaZero) (s : ℂ) :
    zetaCanonicalProduct s = genusOne (s/r.val) ^ analyticOrderNatAt riemannZeta r.val *
      zetaSubproduct (zeroFiber r)ᶜ s := by
  have h (A : Set RepeatedZetaZero) :
      Multipliable ((fun i => zetaFactor i s) ∘ ((↑) : A → RepeatedZetaZero)) :=
    ((zetaSubproduct_locally_uniform A).hasProd (Set.mem_univ s)).multipliable
  have he := (zeroFiberEquiv r).tprod_eq (fun i : zeroFiber r => zetaFactor i.val s)
  change (∏' _ : Fin (analyticOrderNatAt riemannZeta r.val), genusOne (s/r.val)) = _ at he
  rw [tprod_fintype] at he
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  exact (Multipliable.tprod_mul_tprod_compl (h (zeroFiber r)) (h (zeroFiber r)ᶜ)).symm.trans
    (congrArg (fun a => a*zetaSubproduct (zeroFiber r)ᶜ s) he.symm)

theorem zetaSubproduct_compl_ne_zero (r : NontrivialZetaZero) :
    zetaSubproduct (zeroFiber r)ᶜ r.val ≠ 0 := by
  obtain ⟨u, hu, hb⟩ := zetaFactor_majorant_on_compact {r.val} isCompact_singleton
  let A := (zeroFiber r)ᶜ
  have hm : Summable (fun i : A => ‖zetaFactor i.val r.val-1‖) :=
    (hu.subtype A).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i.val _ (Set.mem_singleton _))
  have he (a : ℂ) : 1+(a-1)=a := by ring
  have hz (i : A) : 1+(zetaFactor i.val r.val-1) ≠ 0 := by
    rw [he]
    intro h
    exact i.property (Subtype.ext ((zetaFactor_eq_zero_iff i.val r.val).mp h).symm)
  simpa only [he, zetaSubproduct] using tprod_one_add_ne_zero_of_summable hz hm

theorem zetaCanonicalProduct_order (r : NontrivialZetaZero) :
    analyticOrderAt zetaCanonicalProduct r.val = analyticOrderAt riemannZeta r.val := by
  obtain ⟨δ,hδ,hd⟩ := zeta_zero_norm_lower
  have hr : r.val ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hd r))
  let m := analyticOrderNatAt riemannZeta r.val
  let E := fun s : ℂ => -(r.val)⁻¹ * Complex.exp (s/r.val)
  have ha : AnalyticAt ℂ E r.val := by dsimp [E]; fun_prop
  have hn : E r.val ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hr)) (Complex.exp_ne_zero _)
  rw [← Nat.cast_analyticOrderNatAt (zeta_nontrivial_zero_finite_order r).2]
  apply (zetaCanonicalProduct_entire _ (Set.mem_univ _)).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun s => E s ^ m * zetaSubproduct (zeroFiber r)ᶜ s,
    (ha.pow m).mul (zetaSubproduct_entire _ _ (Set.mem_univ _)),
    mul_ne_zero (pow_ne_zero _ hn) (zetaSubproduct_compl_ne_zero r), .of_forall ?_⟩
  intro s
  have he : genusOne (s/r.val) = (s-r.val)*E s := by
    unfold genusOne E
    field_simp [hr] <;> ring
  rw [zetaCanonicalProduct_split, he, mul_pow, smul_eq_mul]
  change (s-r.val)^m * E s^m * _ = _
  ring

end RHConnections.CanonicalFactor
