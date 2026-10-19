/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ProjectiveChartCover
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.OriginalClosure
/-! # Exact coordinate equations on the single original quadratic closure -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- The actual closure of the entire original affine scheme has the same ideal as the
single generic-point construction. -/
def quadraticOriginalImageIso :
    (quadraticOriginalMap k R g).image ≅ quadraticProjectiveImage k R g :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (quadraticOriginalMap_ker k R g))

@[reassoc]
theorem quadraticOriginalImageIso_hom_inclusion :
    (quadraticOriginalImageIso k R g).hom ≫
      (quadraticProjectiveGenericMap k R g).imageι = (quadraticOriginalMap k R g).imageι :=
  Scheme.subscheme_eqToHom_inclusion (quadraticOriginalMap_ker k R g)

/-- The global-chart comparison preserves the literal native closed immersion. -/
@[reassoc]
theorem quadraticProjectiveImageChartIso_hom_SpecMap (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    (quadraticProjectiveImageChartIso k R g j hj).hom ≫
      Spec.map (CommRingCat.ofHom (nativeChartMapToRatioRing k R g j hj)) =
        pullback.fst (quadraticChartInclusion k j)
          (quadraticProjectiveGenericMap k R g).imageι := by
  dsimp only [quadraticProjectiveImageChartIso, Iso.trans_hom]
  rw [Category.assoc, nativeChartImageIso_hom_SpecMap,
    Scheme.imageOpenChartIso_hom_inclusion]

/-- The inverse chart map into the single global closure, with no replacement chart. -/
def quadraticRatioChartToImage (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0) :
    Spec (.of (chart k R g j)) ⟶ quadraticProjectiveImage k R g :=
  (quadraticProjectiveImageChartIso k R g j hj).inv ≫ pullback.snd _ _

@[reassoc]
theorem quadraticRatioChartToImage_inclusion (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    quadraticRatioChartToImage k R g j hj ≫ (quadraticProjectiveGenericMap k R g).imageι =
      Spec.map (CommRingCat.ofHom (nativeChartMapToRatioRing k R g j hj)) ≫
        quadraticChartInclusion k j := by
  rw [quadraticRatioChartToImage, Category.assoc, ← pullback.condition,
    ← Category.assoc, ← quadraticProjectiveImageChartIso_hom_SpecMap k R g j hj,
    Iso.inv_hom_id_assoc]

/-- The original hyperplane at infinity becomes exactly the complement of D(h_j),
where h_j is the original inverse monomial, not a substituted coordinate. -/
theorem quadraticRatioChartToImage_preimage_constant (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    quadraticRatioChartToImage k R g j hj ⁻¹ᵁ
      ((quadraticProjectiveGenericMap k R g).imageι ⁻¹ᵁ
        coordinateOpen k (Exponent σ) constantIndex) =
      PrimeSpectrum.basicOpen (infinityCoordinate k R g j) := by
  rw [← Scheme.Hom.comp_preimage, quadraticRatioChartToImage_inclusion,
    Scheme.Hom.comp_preimage, coordinateChart_preimage_coordinateOpen,
    SpecMap_preimage_basicOpen]
  congr 1
  exact nativeChartMapToRatioRing_infinity k R g j hj

end QuadraticIncidence.InfinityChart
