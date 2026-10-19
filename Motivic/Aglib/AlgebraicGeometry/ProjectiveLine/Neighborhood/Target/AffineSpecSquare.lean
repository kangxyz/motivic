/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.BaseChange
/-! # Cartesian coefficient restriction with the literal native affine base

Changing an affine base to its canonical spectrum changes no chosen open or
section. This form of the square composes without normalizing ring-map products.

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.AffineSpecSquare`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`AffineLine.CoefficientCartesianSquare`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] {Y : Scheme.{u}} [IsAffine Y]
  (b : Y ⟶ Spec (.of R))

/-- The same coefficient restriction, with its affine base presented as a spectrum. -/
def nativeAffineBaseRestriction : Spec Γ(Y, ⊤) ⟶ Spec (.of R) :=
  Y.isoSpec.inv ≫ b

/-- The single native line restriction; composites are left as composites. -/
def nativeAffineLineRestriction :
    Spec (.of (Polynomial Γ(Y, ⊤))) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R b)))

/-- The full native affine line is Cartesian over the same native affine base. -/
theorem nativeAffineSpecSquare :
    IsPullback (nativeAffineLineRestriction R b)
      (Spec.map (CommRingCat.ofHom
        (Polynomial.C : Γ(Y, ⊤) →+* Polynomial Γ(Y, ⊤))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
      (nativeAffineBaseRestriction R b) := by
  apply (targetAffineLineSquare R b).of_iso
    (Iso.refl _) (Iso.refl _) Y.isoSpec (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      nativeAffineLineRestriction]
  · simp only [Iso.refl_hom, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, nativeAffineBaseRestriction,
      Iso.hom_inv_id_assoc]

end AlgebraicGeometry.RelativeProjectiveLine
