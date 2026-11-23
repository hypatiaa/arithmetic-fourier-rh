import Verified

open Finset ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

def pairedSeeds (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun d => Odd d ∧ Squarefree d ∧ d.Coprime 165 ∧ X < 22*d ∧ 15*d ≤ X)

def pairedBlock (X : ℕ) : Finset ℕ :=
  ((pairedSeeds X).image (fun d => 11*d)) ∪ ((pairedSeeds X).image (fun d => 15*d))

theorem paired_seed_iff {X d : ℕ} : d ∈ pairedSeeds X ↔
    1 ≤ d ∧ Odd d ∧ Squarefree d ∧ d.Coprime 165 ∧ X < 22*d ∧ 15*d ≤ X := by
  simp only [pairedSeeds,mem_filter,Finset.mem_Icc,and_assoc]
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1, by omega, h.2⟩

private theorem seed_coprime {X d : ℕ} (hd : d ∈ pairedSeeds X) :
    Nat.Coprime 11 d ∧ Nat.Coprime 15 d := by
  have h := (paired_seed_iff.mp hd).2.2.2.1.symm
  change Nat.Coprime (11*15) d at h
  exact Nat.coprime_mul_iff_left.mp h

theorem paired_block_in_shell (X : ℕ) : pairedBlock X ⊆ upperOddShell X := by
  intro n hn
  rw [pairedBlock,Finset.mem_union] at hn
  rcases hn with h | h
  · obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    obtain ⟨hd₁,hdodd,_,_,hlo,hhi⟩ := paired_seed_iff.mp hd
    exact upper_odd_shell_iff.mpr ⟨by omega,by omega,(by decide : Odd (11:ℕ)).mul hdodd,by omega⟩
  · obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    obtain ⟨hd₁,hdodd,_,_,hlo,hhi⟩ := paired_seed_iff.mp hd
    exact upper_odd_shell_iff.mpr ⟨by omega,hhi,(by decide : Odd (15:ℕ)).mul hdodd,by omega⟩

theorem paired_images_disjoint (X : ℕ) :
    Disjoint ((pairedSeeds X).image (fun d => 11*d)) ((pairedSeeds X).image (fun d => 15*d)) := by
  rw [Finset.disjoint_left]
  intro n h₁ h₂
  obtain ⟨d,_,rfl⟩ := mem_image.mp h₁
  obtain ⟨e,he,hee⟩ := mem_image.mp h₂
  have hdiv : 11 ∣ 15*e := ⟨d,hee⟩
  have h11e : 11 ∣ e := (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 11 15)).mp hdiv
  have h := (seed_coprime he).1
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left h11e] at h
  omega

private theorem mobius_eleven_mul {X d : ℕ} (hd : d ∈ pairedSeeds X) :
    muR (11*d) = -muR d := by
  have h := isMultiplicative_moebius.map_mul_of_coprime (seed_coprime hd).1
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide : Nat.Prime 11)
  rw [h11,neg_one_mul] at h
  change (moebius (11*d):ℝ) = -(moebius d:ℝ)
  exact_mod_cast h

private theorem mobius_fifteen_mul {X d : ℕ} (hd : d ∈ pairedSeeds X) :
    muR (15*d) = muR d := by
  have h15 : moebius 15 = 1 := by
    change moebius (3*5) = 1
    rw [isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 3 5),
      moebius_apply_prime Nat.prime_three,moebius_apply_prime (by decide : Nat.Prime 5)]
    norm_num
  have h := isMultiplicative_moebius.map_mul_of_coprime (seed_coprime hd).2
  rw [h15,one_mul] at h
  change (moebius (15*d):ℝ) = (moebius d:ℝ)
  exact_mod_cast h

private theorem image_scale_injective {a : ℕ} (ha : 0 < a) : Function.Injective (fun d : ℕ => a*d) :=
  fun _ _ h => Nat.eq_of_mul_eq_mul_left ha h

theorem paired_block_card (X : ℕ) : (pairedBlock X).card = 2*(pairedSeeds X).card := by
  rw [pairedBlock,card_union_of_disjoint (paired_images_disjoint X),
    card_image_of_injective _ (image_scale_injective (by norm_num : (0:ℕ)<11)),
    card_image_of_injective _ (image_scale_injective (by norm_num : (0:ℕ)<15))]
  omega

theorem paired_block_balanced (X : ℕ) : ∑ n ∈ pairedBlock X, muR n = 0 := by
  rw [pairedBlock,sum_union (paired_images_disjoint X),
    sum_image (image_scale_injective (by norm_num : (0:ℕ)<11)).injOn,
    sum_image (image_scale_injective (by norm_num : (0:ℕ)<15)).injOn,← sum_add_distrib]
  exact sum_eq_zero fun d hd => by rw [mobius_eleven_mul hd,mobius_fifteen_mul hd,neg_add_cancel]

theorem paired_block_unit_squares {X n : ℕ} (hn : n ∈ pairedBlock X) : (muR n)^2 = 1 := by
  rw [pairedBlock,Finset.mem_union] at hn
  rcases hn with h | h
  · obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    rw [mobius_eleven_mul hd,neg_sq]
    have h := moebius_sq_eq_one_of_squarefree (paired_seed_iff.mp hd).2.2.1
    change (moebius d:ℝ)^2 = 1
    exact_mod_cast h
  · obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    rw [mobius_fifteen_mul hd]
    have h := moebius_sq_eq_one_of_squarefree (paired_seed_iff.mp hd).2.2.1
    change (moebius d:ℝ)^2 = 1
    exact_mod_cast h

end RHConnections.ArithmeticFourierShell
