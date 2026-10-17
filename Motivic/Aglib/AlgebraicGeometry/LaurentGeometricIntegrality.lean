/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.LaurentTorus
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Geometric integrality of the affine line and Laurent torus

These instances concern the literal coefficient projections on polynomial and
Laurent polynomial spectra. The polynomial chart is relative affine space;
the Laurent chart is its open subscheme, with a section given by evaluation at
one. Both projections are geometrically integral over every commutative ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- An isomorphism has integral field-valued fibers, including every identity map. -/
instance (priority := low) instGeometricallyIntegralOfIsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : GeometricallyIntegral f := by
  constructor
  intro K _ y Z fst snd h
  have : IsIso snd := h.isIso_snd_of_isIso
  exact IsIntegral.of_isIso (inv snd)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The literal polynomial spectrum is the relative affine line. -/
def polynomialAffineSpaceIso (R : CommRingCat.{u}) :
    Spec (.of (Polynomial R)) ≅ AffineSpace (ULift.{u} Unit) (Spec R) :=
  Scheme.Spec.mapIso
    (MvPolynomial.uniqueAlgEquiv R (ULift.{u} Unit)).toRingEquiv.toCommRingCatIso.op ≪≫
      (AffineSpace.SpecIso (ULift.{u} Unit) R).symm

@[reassoc (attr := simp)]
theorem polynomialAffineSpaceIso_hom_over (R : CommRingCat.{u}) :
    (polynomialAffineSpaceIso R).hom ≫
      (AffineSpace (ULift.{u} Unit) (Spec R) ↘ Spec R) = polynomialProjection R := by
  simp only [polynomialAffineSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (MvPolynomial.uniqueAlgEquiv R (ULift.{u} Unit)).commutes r

/-- Every field-valued base change of the literal polynomial projection is integral. -/
instance instGeometricallyIntegralPolynomialProjection (R : CommRingCat.{u}) :
    GeometricallyIntegral (polynomialProjection R) := by
  have sq : IsPullback (polynomialAffineSpaceIso R).hom (polynomialProjection R)
      (AffineSpace (ULift.{u} Unit) (Spec R) ↘ Spec R) (𝟙 (Spec R)) :=
    IsPullback.of_horiz_isIso
      ⟨by simp only [polynomialAffineSpaceIso_hom_over, Category.comp_id]⟩
  exact MorphismProperty.of_isPullback sq inferInstance

/-- Evaluation at one witnesses surjectivity over every base ring. -/
instance instSurjectiveLaurentProjection (R : CommRingCat.{u}) :
    Surjective (laurentProjection R) := by
  have : Surjective (laurentOneSection R ≫ laurentProjection R) := by
    rw [laurentOneSection_projection]
    infer_instance
  exact Surjective.of_comp (laurentOneSection R) (laurentProjection R)

/-- The Laurent open subscheme remains reduced after every field-valued base change. -/
instance instGeometricallyReducedLaurentProjection (R : CommRingCat.{u}) :
    GeometricallyReduced (laurentProjection R) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let i : pullback (laurentProjection R) y ⟶ pullback (polynomialProjection R) y :=
    pullback.map _ _ _ _ (laurentPlus R) (𝟙 _) (𝟙 _)
      (by simp only [Category.comp_id, laurentPlus_projection]) (by simp)
  exact isReduced_of_isOpenImmersion i

/-- Every field-valued base change of the literal Laurent projection is integral. -/
instance instGeometricallyIntegralLaurentProjection (R : CommRingCat.{u}) :
    GeometricallyIntegral (laurentProjection R) := by
  have : Surjective (laurentPlus R ≫ polynomialProjection R) := by
    rw [laurentPlus_projection]
    infer_instance
  have : GeometricallyIrreducible (laurentProjection R) := by
    rw [← laurentPlus_projection]
    infer_instance
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end AlgebraicGeometry.Scheme.PolynomialLaurent
