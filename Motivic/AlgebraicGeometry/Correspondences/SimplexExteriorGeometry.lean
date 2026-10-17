/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteSimplex
public import Motivic.AlgebraicGeometry.SmoothSiteProducts
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Geometric integrality of the actual algebraic simplex

The barycentric quotient chart identifies the actual simplex with relative
affine space. Its structure morphism is therefore geometrically integral.
In particular, its product with any Noetherian integral support is integral.
The original cosimplicial maps are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The polynomial chart with its variables lifted into the scheme universe. -/
def liftedPolynomialEquiv (n : ℕ) :
    CoordinateRing R n ≃ₐ[R] MvPolynomial (ULift.{u} (Fin n)) R :=
  (polynomialEquiv R n).trans (MvPolynomial.renameEquiv R Equiv.ulift.symm)

/-- The actual barycentric simplex is affine space over its original base. -/
def affineSpaceIso (n : ℕ) :
    Spec (.of (CoordinateRing R n)) ≅
      AffineSpace (ULift.{u} (Fin n)) (Spec (.of R)) :=
  Scheme.Spec.mapIso (liftedPolynomialEquiv R n).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of R)).symm

@[reassoc (attr := simp)]
theorem affineSpaceIso_hom_over (n : ℕ) :
    (affineSpaceIso R n).hom ≫
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of R)) ↘ Spec (.of R)) =
        structureMap R n := by
  simp only [affineSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (liftedPolynomialEquiv R n).symm.commutes r

/-- The simplex remains integral after every field-valued base change. -/
instance structureMap_geometricallyIntegral (n : ℕ) :
    GeometricallyIntegral (structureMap R n) := by
  have sq : IsPullback (affineSpaceIso R n).hom (structureMap R n)
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of R)) ↘ Spec (.of R))
      (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso ⟨by simp only [affineSpaceIso_hom_over, Category.comp_id]⟩
  exact MorphismProperty.of_isPullback sq inferInstance

/-- Smooth-site membership retains the geometric integrality of the original simplex map. -/
instance smoothSiteObj_geometricallyIntegral (n : ℕ) :
    GeometricallyIntegral (smoothSiteObj R n).hom :=
  inferInstanceAs (GeometricallyIntegral (structureMap R n))

/-- Integral finite-type supports stay integral after adjoining a simplex factor. -/
instance integral_product {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V]
    (p : V ⟶ Spec (.of R)) (n : ℕ) :
    IsIntegral (Limits.pullback p (structureMap R n)) := inferInstance

end Motivic.AlgebraicSimplex
