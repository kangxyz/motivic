/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceGenericity

/-!
# Canonical coordinates for an original finite dominant endpoint

The original finite support is affine over the affine parameter line. Its
canonical global-Spec comparison supplies all coordinate data for the proved
going-down face theorem. Endpoint points, projection maps and the original
Cartesian square are unchanged; no coordinate witnesses are supplied.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCoordinates`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCurvePlacement`,
`Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.EndpointPushforward`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {C : Scheme.{u}} [IsIntegral C]
  (f : C ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]

omit [IsDomain A] [IsIntegrallyClosed A] [IsIntegral C] [IsFinite f] [IsDominant f] in
/-- The coordinate map is the literal original morphism under its canonical
Spec comparison, not an independently chosen affine presentation. -/
theorem coordinateMap_spec_eq [IsAffine C] :
    Spec.map (CommRingCat.ofHom (coordinateMap f)) = C.isoSpec.inv ≫ f := by
  rw [← Scheme.isoSpec_inv_naturality f, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- Every generic point of an actual evaluation endpoint of the original
finite dominant integral support lies over the generic point of its base. -/
theorem original_face_generic_over_zero
    {E : Scheme.{u}} (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
    (hsq : IsPullback e b f
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
    (x : E) (hx : x ∈ genericPoints E) : b x = (⊥ : PrimeSpectrum A) := by
  let : IsAffine C := isAffine_of_isAffineHom f
  let : Nonempty (⊤ : C.Opens) :=
    ⟨⟨genericPoint C, TopologicalSpace.Opens.mem_top (genericPoint C)⟩⟩
  let : IsDomain Γ(C, ⊤) := IsIntegral.component_integral ⊤
  let φ := coordinateMap f
  have hfinite : φ.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv.symm.surjective)
  have hinj : Function.Injective φ := by
    let : IsSchemeTheoreticallyDominant f := .of_isDominant f
    have hf : Function.Injective f.appTop := by
      simpa [Scheme.Hom.appTop] using f.app_injective ⊤
    exact hf.comp (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv.symm.injective
  have hcoord : IsPullback C.isoSpec.hom f
      (Spec.map (CommRingCat.ofHom φ)) (𝟙 (Spec (.of A[X]))) :=
    IsPullback.of_horiz_isIso ⟨by rw [coordinateMap_spec_eq]; simp⟩
  have hface : IsPullback (e ≫ C.isoSpec.hom) b
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) := by
    simpa only [Category.comp_id] using hsq.paste_horiz hcoord
  exact face_generic_over_zero φ hinj hfinite (e ≫ C.isoSpec.hom) b a hface x hx

/-- The original endpoint map into a finite target endpoint sends every
component generic point to a component generic point. All coordinate and
minimal-prime data have been constructed from the original support map. -/
theorem original_face_generic_image_generic
    {E F : Scheme.{u}} (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
    (hsq : IsPullback e b f
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
    (q : F ⟶ Spec (.of A)) [IsFinite q] (r : E ⟶ F) (hr : r ≫ q = b)
    (x : E) (hx : x ∈ genericPoints E) : r x ∈ genericPoints F := by
  apply _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_image_generic q (r x)
  have hzero : q (r x) = (⊥ : PrimeSpectrum A) := by
    rw [← Scheme.Hom.comp_apply, hr]
    exact original_face_generic_over_zero f e b a hsq x hx
  rw [hzero]
  exact (_root_.AlgebraicGeometry.Scheme.spec_mem_genericPoints_iff_minimalPrime A ⊥).mpr (by
    change (⊥ : Ideal A) ∈ (⊥ : Ideal A).minimalPrimes
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _)

end AlgebraicGeometry.Scheme.FiniteDominantFace
