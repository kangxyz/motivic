/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFacePlacement
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes

/-!
# Genericity of the original finite dominant face

The actual evaluation pullback gives the support of the full endpoint. Its
component generic points yield minimal primes over the literal extended face
ideal. Going down uses normality of the base only. Finite target endpoint maps
then reflect genericity, without flatness or normality of either support.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceGenericity`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCoordinates`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A S : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing S] [IsDomain S]
  (φ : A[X] →+* S) (hφ : Function.Injective φ) (hfinite : φ.Finite)
  {E : Scheme.{u}} (e : E ⟶ Spec (.of S)) (b : E ⟶ Spec (.of A)) (a : A)
  (hsq : IsPullback e b (Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))

include hsq

omit [IsDomain A] [IsIntegrallyClosed A] [IsDomain S] in
/-- The full original endpoint has exactly the support of the extended face
ideal. No reduced replacement or independently assumed kernel is used. -/
theorem mem_range_face_iff (s : Spec (.of S)) :
    s ∈ Set.range e ↔
      (Ideal.span {Polynomial.X - Polynomial.C a}).map φ ≤ s.asIdeal := by
  have hr : Set.range e = (Spec.map (CommRingCat.ofHom φ)) ⁻¹'
      Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨b x, (congrArg (fun f : E ⟶ Spec (.of A[X]) => f x) hsq.w).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, -⟩ := Scheme.exists_preimage_of_isPullback hsq z y hy.symm
      exact ⟨x, hx⟩
  rw [hr]
  change PrimeSpectrum.comap φ s ∈
    Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom a)) ↔ _
  rw [range_comap_of_surjective _ _ (Polynomial.eval_surjective a)]
  change RingHom.ker (Polynomial.evalRingHom a) ≤ s.asIdeal.comap φ ↔ _
  rw [Polynomial.ker_evalRingHom, Ideal.map_le_iff_le_comap]

omit [IsDomain A] [IsIntegrallyClosed A] [IsDomain S] in
/-- An actual generic point of the unreduced endpoint gives a minimal prime
of its original extended evaluation ideal. -/
theorem face_generic_mem_minimalPrimes (x : E) (hx : x ∈ genericPoints E) :
    (e x).asIdeal ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map φ).minimalPrimes := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) :=
    IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective a)
  let : IsClosedImmersion e := MorphismProperty.of_isPullback hsq.flip inferInstance
  refine ⟨⟨inferInstance, (mem_range_face_iff φ e b a hsq (e x)).mp ⟨x, rfl⟩⟩, ?_⟩
  intro Q hQ hQx
  obtain ⟨y, hy⟩ := (mem_range_face_iff φ e b a hsq ⟨Q, hQ.1⟩).mpr hQ.2
  have hspec : e y ⤳ e x := by
    rw [hy]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hQx
  have hyx : y ⤳ x := e.isEmbedding.isInducing.specializes_iff.mp hspec
  have hxy : x ⤳ y := specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure hyx.closure_subset)
  have heq : y = x := (hyx.antisymm hxy).eq
  subst y
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal hy)

include hφ hfinite

/-- Every original endpoint component lies over the generic point of the
unchanged normal base. Normality of the finite support is not assumed. -/
theorem face_generic_over_zero (x : E) (hx : x ∈ genericPoints E) :
    b x = (⊥ : PrimeSpectrum A) := by
  have hminimal := face_generic_mem_minimalPrimes φ e b a hsq x hx
  simpa only [Category.id_comp] using
    face_point_over_zero φ hφ hfinite b (𝟙 E) e a
      (by simpa only [Category.id_comp] using hsq) x hminimal

/-- A finite target endpoint over the same base receives actual endpoint
component generic points generically. This excludes vertical image terms by
proved placement, not by flatness of the support. -/
theorem face_generic_image_generic {F : Scheme.{u}}
    (q : F ⟶ Spec (.of A)) [IsFinite q] (r : E ⟶ F) (hr : r ≫ q = b)
    (x : E) (hx : x ∈ genericPoints E) : r x ∈ genericPoints F := by
  apply _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_image_generic q (r x)
  have hzero : q (r x) = (⊥ : PrimeSpectrum A) := by
    rw [← Scheme.Hom.comp_apply, hr]
    exact face_generic_over_zero φ hφ hfinite e b a hsq x hx
  rw [hzero]
  exact (_root_.AlgebraicGeometry.Scheme.spec_mem_genericPoints_iff_minimalPrime A ⊥).mpr
    (by
      change (⊥ : Ideal A) ∈ (⊥ : Ideal A).minimalPrimes
      rw [Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _)

end AlgebraicGeometry.Scheme.FiniteDominantFace
