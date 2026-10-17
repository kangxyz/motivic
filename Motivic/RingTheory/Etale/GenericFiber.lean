/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Unramified.Field

/-!
# Generic algebras of essentially finite-type unramified algebras

The generic algebra is written with the original algebra on the left, so its
natural algebra structure over that algebra agrees with the integral-closure
comparison map. The field-based proofs are transported from the opposite
orientation by the tensor symmetry. Essential finite type is retained even
when the original algebra is a localization.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Motivic

/-- The generic algebra of an essentially finite-type formally unramified
algebra over a domain is reduced, with the original algebra on the left. -/
theorem isReduced_tensorProduct_fractionRing_of_formallyUnramified
    (R : Type u) (C : Type v) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Algebra.EssFiniteType R C]
    [Algebra.FormallyUnramified R C] : IsReduced (C ⊗[R] FractionRing R) := by
  have : IsReduced (FractionRing R ⊗[R] C) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing R) _
  exact isReduced_of_injective (Algebra.TensorProduct.comm R C (FractionRing R))
    (Algebra.TensorProduct.comm R C (FractionRing R)).injective

/-- The generic algebra of an essentially finite-type formally unramified
algebra over a domain is Artinian. No finiteness over the domain is asserted. -/
theorem isArtinianRing_tensorProduct_fractionRing_of_formallyUnramified
    (R : Type u) (C : Type v) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Algebra.EssFiniteType R C]
    [Algebra.FormallyUnramified R C] : IsArtinianRing (C ⊗[R] FractionRing R) := by
  have := Algebra.FormallyUnramified.finite_of_free
    (FractionRing R) (FractionRing R ⊗[R] C)
  have := IsArtinianRing.of_finite (FractionRing R) (FractionRing R ⊗[R] C)
  exact (Algebra.TensorProduct.comm R (FractionRing R) C).surjective.isArtinianRing

/-- Flatness embeds an algebra into its scalar extension to the total
fraction ring of the base. No domain hypothesis is needed for this injection. -/
theorem algebraMap_tensorProduct_fractionRing_injective_of_flat
    (R : Type u) (C : Type v) [CommRing R] [CommRing C]
    [Algebra R C] [Module.Flat R C] :
    Function.Injective (algebraMap C (C ⊗[R] FractionRing R)) := by
  exact Algebra.TensorProduct.includeLeft_injective (S := C)
    (IsFractionRing.injective R (FractionRing R))

end Motivic
