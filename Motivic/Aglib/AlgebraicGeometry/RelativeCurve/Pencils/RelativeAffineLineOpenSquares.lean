/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeAffineLineOpenMaps
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.OpenRestriction
/-! # The original coefficient square for punctured relative-line opens -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]

/-- Both paths are the same literal coefficient map on the original open schemes. -/
theorem punctured_open_square (φ : R →ₐ[k] S) (W : (Spec (.of R[X])).Opens)
    (hWX : W ≤ principalOpen X) (g : S[X])
    (hWg : principalOpen (X * g) ≤ (lineMap φ).left ⁻¹ᵁ W) :
    narrowInclusion (k := k) X g ≫ puncturedBaseMap φ =
      openMapOfLE φ W (principalOpen (X * g)) hWg ≫
        originalInclusion (k := k) (principalOpen X) W hWX := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (principalOpen (X : R[X])).ι).mp
  have h1 : (narrowInclusion (k := k) X g).left ≫ (principalOpen (X : S[X])).ι =
      (principalOpen (X * g)).ι :=
    Scheme.homOfLE_ι _ (PrimeSpectrum.basicOpen_mul_le_left X g)
  have h2 : (puncturedBaseMap φ).left ≫ (principalOpen (X : R[X])).ι =
      (principalOpen (X : S[X])).ι ≫ (lineMap φ).left :=
    openMapOfLE_inclusion _ _ _ _
  have h3 : (originalInclusion (k := k) (principalOpen X) W hWX).left ≫
      (principalOpen (X : R[X])).ι = W.ι := Scheme.homOfLE_ι _ hWX
  have h4 := openMapOfLE_inclusion φ W (principalOpen (X * g)) hWg
  change ((_ ≫ _) ≫ _) = ((_ ≫ _) ≫ _)
  rw [Category.assoc, h2, ← Category.assoc, h1, Category.assoc, h3, h4]

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
