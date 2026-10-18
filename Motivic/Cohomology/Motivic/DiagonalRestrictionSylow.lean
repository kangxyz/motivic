/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestrictionDegree
public import Aglib.FieldTheory.SylowFixedField

/-! # Actual diagonal cohomology is detected by the full Sylow restriction family -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic.DiagonalRestrictionSylow
open PresheafWithTransfers DiagonalCorestriction
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- Actual finite-transfer degree laws imply joint Sylow detection on the original raw group.
No symbol surjectivity, Milnor comparison, or replacement cohomology is used. -/
theorem eq_zero_of_sylow_restrictions (n : ℕ)
    (x : (motivicRawBaseComplex k n).homology n)
    (hx : ∀ (p : ℕ) (_hp : p.Prime), ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      HomologicalComplex.homologyMap
        (motivicRawBaseComplexMap (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n) n x = 0) :
    x = 0 := by
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hx p hp
  let L := IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))
  have hdeg : (Module.finrank k L : ℤ) • x = 0 := by
    rw [← corestriction_fieldChange (E := L), hS, map_zero]
  have hdiv : addOrderOf x ∣ Module.finrank k L :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa only [natCast_zsmul] using hdeg)
  exact (hp.coprime_iff_not_dvd.mp
    (IntermediateField.coprime_finrank_sylow_fixedField p S)) (hpd.trans hdiv)

/-- Equality of genuine diagonal classes descends through actual Sylow coefficient fields. -/
theorem eq_of_sylow_restrictions (n : ℕ)
    (x y : (motivicRawBaseComplex k n).homology n)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime), ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      HomologicalComplex.homologyMap
        (motivicRawBaseComplexMap (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n) n x =
      HomologicalComplex.homologyMap
        (motivicRawBaseComplexMap (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n) n y) :
    x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_sylow_restrictions k Ω n (x - y)
  intro p hp
  obtain ⟨S, hS⟩ := hxy p hp
  exact ⟨S, by rw [map_sub, hS, sub_self]⟩

end Motivic.DiagonalRestrictionSylow
