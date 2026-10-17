/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Projection
public import Motivic.AlgebraicGeometry.SmoothSiteTorus

/-!
# Literal maps defining contraction

The restriction is the actual polynomial-to-Laurent open immersion. The unit
section is evaluation of the Laurent variable at one, and the auxiliary base
product is identified with the original object by its actual projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.SmoothSite

variable (R : CommRingCat.{u})

/-- The actual principal open complement of zero in the affine line. -/
def torusInAffineLine : torus R ⟶ affineLine R :=
  homMk (laurentPlus R) (laurentPlus_projection R)

@[simp] theorem torusInAffineLine_left :
    (torusInAffineLine R).left = laurentPlus R := rfl

instance : IsOpenImmersion (torusInAffineLine R).left :=
  inferInstanceAs (IsOpenImmersion (laurentPlus R))

/-- The actual structural map of a smooth-site object. -/
def toBase (X : SmoothSite (Spec R)) : X ⟶ base (Spec R) :=
  homMk X.hom (Category.comp_id _)

@[reassoc (attr := simp)] theorem comp_toBase {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    f ≫ toBase R Y = toBase R X :=
  MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f)

/-- The canonical identification of the literal base product with its first factor. -/
def productBaseIso (X : SmoothSite (Spec R)) : product X (base (Spec R)) ≅ X where
  hom := productFst X (base (Spec R))
  inv := productLift (𝟙 X) (toBase R X)
  hom_inv_id := by
    apply product_hom_ext
    · simp
    · simp only [Category.assoc, productLift_snd, Category.id_comp]
      apply MorphismProperty.Over.Hom.ext
      change CategoryTheory.Limits.pullback.fst X.hom (𝟙 _) ≫ X.hom =
        CategoryTheory.Limits.pullback.snd X.hom (𝟙 _)
      simpa using (CategoryTheory.Limits.pullback.condition (f := X.hom) (g := 𝟙 _))
  inv_hom_id := productLift_fst _ _

/-- Product maps to the base retain the literal first projection. -/
@[reassoc (attr := simp)] theorem productMap_toBase {X T : SmoothSite (Spec R)} :
    productMap (𝟙 X) (toBase R T) ≫ (productBaseIso R X).hom = productFst X T := by
  exact (productMap_fst _ _).trans (Category.comp_id _)

/-- The Laurent unit maps to the affine-line point one. -/
@[reassoc (attr := simp)] theorem torusOne_inAffineLine :
    torusOne R ≫ torusInAffineLine R = affineLinePoint R 1 := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change laurentEvalOne R (Polynomial.toLaurent (Polynomial.C r)) =
      Polynomial.eval 1 (Polynomial.C r)
    simp
  · simp [laurentEvalOne, Polynomial.toLaurent_X, LaurentPolynomial.eval₂_T]

/-- The literal punctured affine-line cylinder. -/
def torusCylinder (X : SmoothSite (Spec R)) : SmoothSite (Spec R) :=
  product X (torus R)

/-- Open restriction used in the definition of contraction. -/
def contractionOpen (X : SmoothSite (Spec R)) : torusCylinder R X ⟶ a1Cylinder R X :=
  productMap (𝟙 X) (torusInAffineLine R)

/-- The actual unit section of the punctured cylinder. -/
def torusUnitSection (X : SmoothSite (Spec R)) : X ⟶ torusCylinder R X :=
  productLift (𝟙 X) (toBase R X ≫ torusOne R)

@[reassoc (attr := simp)] theorem torusUnitSection_projection (X : SmoothSite (Spec R)) :
    torusUnitSection R X ≫ productFst X (torus R) = 𝟙 X := productLift_fst _ _

@[reassoc (attr := simp)] theorem torusUnitSection_open (X : SmoothSite (Spec R)) :
    torusUnitSection R X ≫ contractionOpen R X = a1Section R X 1 := by
  apply product_hom_ext
  · simp [contractionOpen, a1Section]
  · simp [contractionOpen, torusUnitSection, a1Section, toBase]

@[reassoc (attr := simp)] theorem baseProduct_unit (X : SmoothSite (Spec R)) :
    (productBaseIso R X).inv ≫ productMap (𝟙 X) (torusOne R) =
      torusUnitSection R X := by
  apply product_hom_ext <;> simp [productBaseIso, torusUnitSection]

end Motivic.SmoothSite
