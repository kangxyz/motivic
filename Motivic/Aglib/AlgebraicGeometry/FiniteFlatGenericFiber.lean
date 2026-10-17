/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.GenericFiniteSectionSpread
public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Generic points of the original finite flat scheme, without reducedness -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GenericSection
variable (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]

instance genericMap_preimmersion : IsPreimmersion (genericMap R) :=
  IsPreimmersion.of_isLocalization (nonZeroDivisors R)

lemma genericMap_range : Set.range (genericMap R) = {genericPoint (Spec (.of R))} := by
  have he (x : Spec (.of (FractionRing R))) : genericMap R x = genericPoint (Spec (.of R)) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    have hx : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim x (⊥ : PrimeSpectrum (FractionRing R)))
    change Ideal.comap (algebraMap R (FractionRing R)) x.asIdeal = ⊥
    rw [hx, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R (FractionRing R))
  ext x
  exact ⟨fun ⟨y, hy⟩ => hy ▸ he y,
    fun hx => ⟨(⊥ : PrimeSpectrum (FractionRing R)),
      (he (⊥ : PrimeSpectrum (FractionRing R))).trans hx.symm⟩⟩

variable [IsFinite (baseMap R B)] [Flat (baseMap R B)]

lemma baseMap_generic_iff (p : Spec (.of B)) :
    baseMap R B p = genericPoint (Spec (.of R)) ↔ p ∈ genericPoints (Spec (.of B)) := by
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
    Motivic.image_mem_genericPoints_iff_of_generalizing (baseMap R B)
      (Flat.generalizingMap (baseMap R B)) p

lemma genericFiber_range :
    Set.range (pullback.fst (baseMap R B) (genericMap R)) = genericPoints (Spec (.of B)) := by
  rw [Scheme.Pullback.range_fst, genericMap_range]
  ext p
  exact baseMap_generic_iff R B p

lemma generic_comap_eq_bot (p : genericPoints (Spec (.of B))) :
    Ideal.comap (algebraMap R B) p.val.asIdeal = ⊥ := by
  have h := (baseMap_generic_iff R B p.val).mpr p.property
  rw [genericPoint_eq_bot_of_affine] at h
  exact congrArg PrimeSpectrum.asIdeal h

instance genericFiber_locallyNoetherian : IsLocallyNoetherian (genericFiber R B) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (baseMap R B) (genericMap R))

end AlgebraicGeometry.Scheme.GenericSection
