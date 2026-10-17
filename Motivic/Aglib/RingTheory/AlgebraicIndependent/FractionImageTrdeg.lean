module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Transcendence degree from images containing a fraction-ring source

If a subalgebra of a fraction field contains the image of the original domain,
the fraction field is algebraic over that subalgebra. Consequently an actual
algebra homomorphism whose image contains the domain bounds the transcendence
degree of the fraction field, without assuming algebraicity or injectivity of
the homomorphism.
-/

@[expose] public noncomputable section

universe u

namespace Subalgebra

/-- A fraction field is algebraic over every subalgebra containing the image
of the original domain. No algebra structure from the coefficient field to the
original domain is required. -/
theorem isAlgebraic_of_fractionRing_image_subset
    {K C E : Type u} [Field K] [CommRing C] [IsDomain C] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra K E]
    (S : Subalgebra K E) (hS : Set.range (algebraMap C E) ⊆ S) :
    Algebra.IsAlgebraic S E := by
  let f : C →+* S := (algebraMap C E).codRestrict S fun c => hS ⟨c, rfl⟩
  let : Algebra C S := f.toAlgebra
  have : IsScalarTower C S E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic C E := IsLocalization.isAlgebraic E (nonZeroDivisors C)
  exact Algebra.IsAlgebraic.extendScalars (R := C) (S := S)
    (fun a b h => IsFractionRing.injective C E (congrArg Subtype.val h))

/-- Containing the source-domain image forces equality with the fraction
field's actual transcendence degree. -/
theorem trdeg_eq_of_fractionRing_image_subset
    {K C E : Type u} [Field K] [CommRing C] [IsDomain C] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra K E]
    (S : Subalgebra K E) (hS : Set.range (algebraMap C E) ⊆ S) :
    Algebra.trdeg K S = Algebra.trdeg K E := by
  have : Algebra.IsAlgebraic S E := S.isAlgebraic_of_fractionRing_image_subset hS
  simpa only [trdeg_eq_zero, add_zero] using trdeg_add_eq K S (A := E)

end Subalgebra

namespace AlgHom

/-- An actual map to a fraction field bounds its transcendence degree whenever
the map's range contains the original domain. The source may have nilpotents
and the map need not be injective. -/
theorem trdeg_le_of_fractionRing_image_subset
    {K C D E : Type u} [Field K] [CommRing C] [IsDomain C] [CommRing D] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra K D] [Algebra K E]
    (f : D →ₐ[K] E) (hf : Set.range (algebraMap C E) ⊆ f.range) :
    Algebra.trdeg K E ≤ Algebra.trdeg K D := by
  rw [← f.range.trdeg_eq_of_fractionRing_image_subset hf]
  exact trdeg_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- Pointwise-image version for a specialized map. It is enough to lift each
original domain element separately into the map's range. -/
theorem trdeg_le_of_fractionRing_image_mem
    {K C D E : Type u} [Field K] [CommRing C] [IsDomain C] [CommRing D] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra K D] [Algebra K E]
    (f : D →ₐ[K] E) (hf : ∀ c : C, algebraMap C E c ∈ f.range) :
    Algebra.trdeg K E ≤ Algebra.trdeg K D :=
  f.trdeg_le_of_fractionRing_image_subset (by rintro _ ⟨c, rfl⟩; exact hf c)

end AlgHom
