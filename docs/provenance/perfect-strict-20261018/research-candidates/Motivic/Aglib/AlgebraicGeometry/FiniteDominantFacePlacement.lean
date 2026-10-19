/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteDominantFacePrimes
public import Motivic.Aglib.AlgebraicGeometry.GenericFiberFiniteSupportCoheight
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Placement of an original finite-family face point

The actual Cartesian face square supplies finiteness of the whole face support.
Going down places a minimal face prime over the generic point of the unchanged
base. Native pullback points then place that same point on the generic fibre,
where the original projection stalk equivalence gives coheight one. Neither the
face support nor its local lengths are replaced by their reductions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A S : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing S] [IsDomain S]
  (φ : A[X] →+* S) (hφ : Function.Injective φ) (hfinite : φ.Finite)
  {E V : Scheme.{u}} (q : V ⟶ Spec (.of A)) (i : E ⟶ V)
  (e : E ⟶ Spec (.of S)) (a : A)
  (hsq : IsPullback e (i ≫ q) (Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))

include hφ hfinite hsq

/-- The original face point lies over the exact zero prime of the original base. -/
theorem face_point_over_zero (x : E)
    (hx : (e x).asIdeal ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map φ).minimalPrimes) :
    (i ≫ q) x = (⊥ : PrimeSpectrum A) := by
  have : (Ideal.span {Polynomial.X - Polynomial.C a} : Ideal A[X]).IsPrime := by
    rw [← Polynomial.ker_evalRingHom]
    exact RingHom.ker_isPrime (Polynomial.evalRingHom a)
  have hcontract := Ideal.comap_eq_of_mem_minimalPrimes_map_prime φ hφ hfinite
    (Ideal.span {Polynomial.X - Polynomial.C a}) (e x).asIdeal hx
  have hpoint : (Spec.map (CommRingCat.ofHom φ)) (e x) =
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) ((i ≫ q) x) :=
    congrArg (fun f : E ⟶ Spec (.of A[X]) => f x) hsq.w
  have hconstants := congrArg
    (fun z : Spec (.of A[X]) => z.asIdeal.comap (Polynomial.C : A →+* A[X])) hpoint
  change ((e x).asIdeal.comap φ).comap Polynomial.C =
    (((i ≫ q) x).asIdeal.comap (Polynomial.evalRingHom a)).comap Polynomial.C
      at hconstants
  rw [hcontract, ← Polynomial.ker_evalRingHom, RingHom.comap_ker] at hconstants
  have heval : (Polynomial.evalRingHom a).comp (Polynomial.C : A →+* A[X]) =
      RingHom.id A := by ext b; simp
  have hid : RingHom.ker (RingHom.id A) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id
  rw [heval, hid, Ideal.comap_comap, heval, Ideal.comap_id] at hconstants
  exact PrimeSpectrum.ext hconstants.symm

/-- The same original face point has a lift to the full generic-fibre support.
The equation keeps the literal original point, not merely its residue field. -/
theorem exists_genericFiber_support_point
    (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]
    (x : E)
    (hx : (e x).asIdeal ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map φ).minimalPrimes) :
    ∃ y : LocalRing.GenericFiber.support A F q i,
      pullback.fst i (LocalRing.GenericFiber.projection A F q) y = x := by
  have hzero := face_point_over_zero φ hφ hfinite q i e a hsq x hx
  have hfield : LocalRing.GenericFiber.baseMap A F (⊥ : PrimeSpectrum F) =
      (⊥ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A F)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback q (LocalRing.GenericFiber.baseMap A F))
    (i x) (⊥ : PrimeSpectrum F) (hzero.trans hfield.symm)
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback i (LocalRing.GenericFiber.projection A F q)) x z hz.symm
  exact ⟨y, hy⟩

/-- Original endpoint-support points selected by face minimality have coheight
one in the original smooth curve. Finite double cuts are not assumed here. -/
theorem face_point_coheight [IsClosedImmersion i] [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] (F : Type u) [Field F]
    [Algebra A F] [IsFractionRing A F] (x : E)
    (hx : (e x).asIdeal ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map φ).minimalPrimes) :
    coheight (i x) = 1 := by
  have : IsFinite (Spec.map (CommRingCat.ofHom φ)) :=
    (IsFinite.SpecMap_iff _).mpr hfinite
  have : IsFinite (i ≫ q) := MorphismProperty.of_isPullback hsq inferInstance
  obtain ⟨y, hy⟩ := exists_genericFiber_support_point φ hφ hfinite q i e a hsq F x hx
  have hp : LocalRing.GenericFiber.projection A F q
      (LocalRing.GenericFiber.supportInclusion A F q i y) = i x := by
    have h := congrArg (fun f : LocalRing.GenericFiber.support A F q i ⟶ V => f y)
      (pullback.condition (f := i) (g := LocalRing.GenericFiber.projection A F q))
    simpa only [Scheme.Hom.comp_apply, hy] using h.symm
  simpa only [hp] using LocalRing.GenericFiber.support_image_coheight A F q i y

end AlgebraicGeometry.Scheme.FiniteDominantFace
