/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.SerrePair
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.Divisors
/-! # The Serre open is exactly the original base shrink -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]

lemma neighborhoodProjective_base :
    (neighborhoodProjectiveIso R V).hom ≫ ProjectiveSpace.toSpec _ _ ≫
      Spec.map (CommRingCat.ofHom (Scheme.ConstantCurve.coefficientMap
        (neighborhoodAffineBase R V))) =
    pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ≫
      neighborhoodProjection R V := by
  simp only [Scheme.ConstantCurve.map_coefficientMap, neighborhoodAffineBase,
    neighborhoodProjectiveIso_toSpec_assoc, Category.assoc, Iso.hom_inv_id_assoc]

lemma neighborhoodSerreOpen_eq_compact (r : R) :
    (neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r =
      neighborhoodCompactOpen R V r := by
  have h := congrArg (fun f => f ⁻¹ᵁ PrimeSpectrum.basicOpen r)
    (neighborhoodProjective_base R V)
  have hb : Spec.map (CommRingCat.ofHom
      (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen
          (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V) r) := by
    ext x
    rfl
  simpa only [Scheme.Hom.comp_preimage, hb, neighborhoodSerreOpen,
    neighborhoodCompactOpen, neighborhoodSourceOpen] using h
end AlgebraicGeometry.RelativeProjectiveLine
