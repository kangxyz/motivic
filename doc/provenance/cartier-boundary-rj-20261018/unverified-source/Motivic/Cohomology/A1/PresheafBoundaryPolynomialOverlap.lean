/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PuncturedCylinderCoordinates
public import Motivic.Cohomology.A1.ContractionBoundaryGeometry
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # The original polynomial overlap restricts the actual boundary section -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {R : Type u} [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  (v : AffineTorusPolynomialPresentation.affineSite k R ⟶ X)

/-- The original polynomial puncture maps to the original torus, with both coordinates retained. -/
def polynomialPunctureToTorus :
    RelativePolynomialOpenSpans.openSite (k := k) (Polynomial.X : Polynomial R) ⟶
      SmoothSite.torusCylinder (.of k) X :=
  (RelativePolynomialOpenSpans.puncturedProductIso (k := k) (R := R)).hom ≫
    SmoothSite.productMap v (𝟙 (SmoothSite.torus (.of k)))

/-- This is the unchanged original puncture inclusion over the original base. -/
@[reassoc] theorem polynomialPunctureToTorus_open :
    polynomialPunctureToTorus X v ≫ SmoothSite.contractionOpen (.of k) X =
      RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R) ≫
        (SmoothSiteAffineCoordinates.lineCylinderIso (k := k) (R := R)).hom ≫
          SmoothSite.a1Map (.of k) v := by
  rw [polynomialPunctureToTorus, Category.assoc,
    ← SmoothSite.contractionOpen_naturality, ← Category.assoc,
    RelativePolynomialOpenSpans.puncturedProductIso_open, Category.assoc]

variable (W : FiniteEtaleSite (SmoothSite.a1Cylinder (.of k) X).left)
  {Y : SmoothSite (Spec (.of k))}
  (p : Y ⟶ RelativePolynomialOpenSpans.lineSite (k := k) (R := R)) [Etale p.left]
  (e : Y ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W)
  (hp : p ≫ (SmoothSiteAffineCoordinates.lineCylinderIso (k := k) (R := R)).hom ≫
    SmoothSite.a1Map (.of k) v = e ≫ toBase (SmoothSite.a1Cylinder (.of k) X) W)

/-- The actual original overlap maps to the actual original punctured small-site
neighborhood, before restricting any section of P. -/
def polynomialOverlapToPunctured :
    SmoothSite.etalePullback p
      (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)) ⟶
    (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W) := by
  let a := RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)
  let l := SmoothSite.etalePullbackFst p a
  let n := SmoothSite.etalePullbackSnd p a
  have hc : (l ≫ e) ≫ toBase (SmoothSite.a1Cylinder (.of k) X) W =
      (n ≫ polynomialPunctureToTorus X v) ≫ SmoothSite.contractionOpen (.of k) X := by
    have hPB := (SmoothSite.etalePullbackCone p a).condition
    rw [Category.assoc, ← hp, ← Category.assoc l p, hPB]
    simp only [Category.assoc, polynomialPunctureToTorus_open]
  exact SmoothSite.homMk
    (pullback.lift (l.left ≫ e.left) (n.left ≫ (polynomialPunctureToTorus X v).left)
      (congrArg (fun f => f.left) hc)) (by
        change pullback.lift _ _ _ ≫
          (pullback.snd W.hom (SmoothSite.contractionOpen (.of k) X).left ≫
            (SmoothSite.torusCylinder (.of k) X).hom) = _
        rw [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w (n ≫ polynomialPunctureToTorus X v))

/-- Original ambient projection of the original overlap restriction. -/
@[reassoc] theorem polynomialOverlapToPunctured_fst :
    (polynomialOverlapToPunctured X v W p e hp).left ≫
      pullback.fst W.hom (SmoothSite.contractionOpen (.of k) X).left =
    (SmoothSite.etalePullbackFst p
      (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R))).left ≫
        e.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- Original torus projection of that same overlap restriction. -/
@[reassoc] theorem polynomialOverlapToPunctured_snd :
    (polynomialOverlapToPunctured X v W p e hp).left ≫
      pullback.snd W.hom (SmoothSite.contractionOpen (.of k) X).left =
    (SmoothSite.etalePullbackSnd p
      (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R))).left ≫
        (polynomialPunctureToTorus X v).left := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

end Motivic.FiniteEtaleSite.OriginalPresheaf
