/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ProjectiveImage
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PrincipalOpen
/-! # Literal original coordinates on the actual quadratic image charts -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.Scheme
lemma affineImageSectionMap_imageι {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (z : A) :
    affineImageSectionMap φ ((Spec.map (CommRingCat.ofHom φ)).imageι.appTop
      ((ΓSpecIso (.of A)).inv z)) = φ z :=
  congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom z)
    (affineImageSectionMap_comp φ)
end AlgebraicGeometry.Scheme
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R) (j : Exponent σ)

/-- The original native chart map corestricted to its actual monomial-ratio algebra. -/
def nativeChartMapToRatioRing (hj : monomialFunction k R g j ≠ 0) :
    coordinateRing k (Exponent σ) j →+* chart k R g j :=
  (nativeDehomogenization k R g j).codRestrict (chart k R g j).toSubring fun z => by
    rw [← nativeDehomogenization_range k R g j hj]
    exact ⟨z, rfl⟩

theorem nativeChartImageSectionsEquiv_val (hj : monomialFunction k R g j ≠ 0)
    (z : Γ((nativeChartGenericMap k R g j).image, ⊤)) :
    (nativeChartImageSectionsEquiv k R g j hj z : FractionRing R) =
      Scheme.affineImageSectionMap (nativeDehomogenization k R g j) z := rfl

/-- The affine-image coordinate isomorphism retains the literal original map. -/
theorem nativeChartImageSectionsEquiv_imageι (hj : monomialFunction k R g j ≠ 0)
    (z : coordinateRing k (Exponent σ) j) :
    nativeChartImageSectionsEquiv k R g j hj
      ((nativeChartGenericMap k R g j).imageι.appTop
        ((Scheme.ΓSpecIso (.of (coordinateRing k (Exponent σ) j))).inv z)) =
      nativeChartMapToRatioRing k R g j hj z := by
  apply Subtype.ext
  rw [nativeChartImageSectionsEquiv_val]
  change Scheme.affineImageSectionMap _ _ = nativeDehomogenization k R g j z
  exact Scheme.affineImageSectionMap_imageι (nativeDehomogenization k R g j) z

/-- In particular the actual homogenizing coordinate maps to the original inverse pivot. -/
theorem nativeChartMapToRatioRing_infinity (hj : monomialFunction k R g j ≠ 0) :
    nativeChartMapToRatioRing k R g j hj
      (coordinateRatio k (Exponent σ) j constantIndex) = infinityCoordinate k R g j := by
  apply Subtype.ext
  change nativeDehomogenization k R g j
    (coordinateRatio k (Exponent σ) j constantIndex) = _
  rw [nativeDehomogenization_ratio k R g j constantIndex hj, ratio_constant]
  rfl

/-- The affine chart isomorphism commutes with the actual inclusion into the native chart. -/
@[reassoc]
theorem nativeChartImageIso_hom_SpecMap (hj : monomialFunction k R g j ≠ 0) :
    (nativeChartImageIso k R g j hj).hom ≫
      Spec.map (CommRingCat.ofHom (nativeChartMapToRatioRing k R g j hj)) =
        (nativeChartGenericMap k R g j).imageι := by
  have : IsAffine (nativeChartGenericMap k R g j).image :=
    isAffine_of_isAffineHom (nativeChartGenericMap k R g j).imageι
  have hr : CommRingCat.ofHom (nativeChartMapToRatioRing k R g j hj) ≫
      (nativeChartImageSectionsEquiv k R g j hj).toCommRingCatIso.inv =
        (Scheme.ΓSpecIso (.of (coordinateRing k (Exponent σ) j))).inv ≫
          (nativeChartGenericMap k R g j).imageι.appTop := by
    ext z
    apply (nativeChartImageSectionsEquiv k R g j hj).injective
    simpa using (nativeChartImageSectionsEquiv_imageι k R g j hj z).symm
  dsimp only [nativeChartImageIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom]
  rw [Category.assoc]
  change (nativeChartGenericMap k R g j).image.isoSpec.hom ≫
    Spec.map (nativeChartImageSectionsEquiv k R g j hj).toCommRingCatIso.inv ≫ _ = _
  rw [← Spec.map_comp, hr, Spec.map_comp, ← Category.assoc,
    Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom, Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id]
  simp only [Spec.map_id, Category.comp_id]

end QuadraticIncidence.InfinityChart
