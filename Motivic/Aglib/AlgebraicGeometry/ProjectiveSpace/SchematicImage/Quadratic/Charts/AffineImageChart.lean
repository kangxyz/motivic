/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.RatioChartMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-! # The native schematic image of the actual quadratic chart map

This identifies the actual affine schematic image, including its structure ring, with the
original monomial-ratio algebra. Projective chart compatibility is handled separately.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

def affineImageSectionMap : Γ((Spec.map (CommRingCat.ofHom φ)).image, ⊤) →+* B :=
  (ΓSpecIso (.of B)).hom.hom.comp (Spec.map (CommRingCat.ofHom φ)).toImage.appTop.hom

theorem affineImageSectionMap_comp :
    (ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).imageι.appTop ≫
      CommRingCat.ofHom (affineImageSectionMap φ) = CommRingCat.ofHom φ := by
  change (ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).imageι.appTop ≫
    (Spec.map (CommRingCat.ofHom φ)).toImage.appTop ≫ (ΓSpecIso (.of B)).hom = _
  rw [← Hom.comp_appTop_assoc, Hom.toImage_imageι, ← ΓSpecIso_inv_naturality_assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem affineImageSectionMap_injective : Function.Injective (affineImageSectionMap φ) := by
  apply (ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.injective.comp
  have h := (Spec.map (CommRingCat.ofHom φ)).toImage_app_injective
    ⟨⊤, isAffineOpen_top _⟩
  simpa only [Hom.preimage_top] using h

theorem affineImageSectionMap_range : (affineImageSectionMap φ).range = φ.range := by
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (Spec.map (CommRingCat.ofHom φ)).imageι).2
  have hc := ConcreteCategory.congr_hom (affineImageSectionMap_comp φ)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hs y
    refine ⟨(ΓSpecIso (.of A)).hom z, ?_⟩
    simpa using (hc ((ΓSpecIso (.of A)).hom z)).symm
  · rintro ⟨y, rfl⟩
    exact ⟨(Spec.map (CommRingCat.ofHom φ)).imageι.appTop ((ΓSpecIso (.of A)).inv y), hc y⟩

/-- Affine schematic-image coordinates retain the literal original ring-map range. -/
def affineImageSectionsEquivRange :
    Γ((Spec.map (CommRingCat.ofHom φ)).image, ⊤) ≃+* φ.range :=
  (RingEquiv.ofBijective (affineImageSectionMap φ).rangeRestrict
    ⟨fun _ _ h => affineImageSectionMap_injective φ (congrArg Subtype.val h),
      (affineImageSectionMap φ).rangeRestrict_surjective⟩).trans
    (RingEquiv.subringCongr (affineImageSectionMap_range φ))

end AlgebraicGeometry.Scheme

open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R) (j : Exponent σ)

/-- The literal map into the native affine projective-chart spectrum. -/
abbrev nativeChartGenericMap := Spec.map (CommRingCat.ofHom (nativeDehomogenization k R g j))

/-- The structure ring of the actual schematic image is exactly the same ratio ring. -/
def nativeChartImageSectionsEquiv (hj : monomialFunction k R g j ≠ 0) :
    Γ((nativeChartGenericMap k R g j).image, ⊤) ≃+* chart k R g j :=
  (Scheme.affineImageSectionsEquivRange (nativeDehomogenization k R g j)).trans
    (RingEquiv.subringCongr (nativeDehomogenization_range k R g j hj))

/-- The actual native schematic image is the spectrum of the monomial-ratio algebra. -/
def nativeChartImageIso (hj : monomialFunction k R g j ≠ 0) :
    (nativeChartGenericMap k R g j).image ≅ Spec (.of (chart k R g j)) := by
  have : IsAffine (nativeChartGenericMap k R g j).image :=
    isAffine_of_isAffineHom (nativeChartGenericMap k R g j).imageι
  exact (nativeChartGenericMap k R g j).image.isoSpec ≪≫
    Scheme.Spec.mapIso (nativeChartImageSectionsEquiv k R g j hj).toCommRingCatIso.symm.op
end QuadraticIncidence.InfinityChart
