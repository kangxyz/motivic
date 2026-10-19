/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.ScalarPolynomialPuncture
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.AmbientIso

/-! # Actual scalar polynomial presentations in native coordinates

Only canonical source and ambient isomorphisms are used. The full mapped
closed scheme, its original lift, and all retained boundary data are unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

local instance : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

local instance : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

local notation "F" => fieldBaseChange (algebraMap k L)
local notation "ρ" => Spec.map (CommRingCat.ofHom
  (algebraMap (Polynomial R) ((Polynomial R) ⊗[k] L)))

/-- The native scalar source is the literal pullback of the original polynomial map. -/
theorem scalarPolynomialSourceSquare {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) :
    IsPullback (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (((F).map (p ≫ (polynomialAffineIso k R).hom)).left ≫
        (affineScalarIso k (Polynomial R) L).hom.left)
      (p ≫ (polynomialAffineIso k R).hom).left ρ :=
  affineScalarMap_isPullback k (Polynomial R) L
    (p ≫ (polynomialAffineIso k R).hom)

/-- The canonical Cartesian source comparison, preserving the original source. -/
def scalarPolynomialSourceIso {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) :
    ((F).obj Y).left ≅ pullback (p ≫ (polynomialAffineIso k R).hom).left ρ :=
  (scalarPolynomialSourceSquare k R L p).isoPullback

/-- The source comparison followed by tensor coordinates is the native scalar map. -/
@[reassoc]
theorem scalarPolynomialSourceIso_native {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) :
    (scalarPolynomialSourceIso k R L p).hom ≫
      pullback.snd (p ≫ (polynomialAffineIso k R).hom).left ρ ≫
      (tensorPolynomialLineIso k R L).hom.left =
        ((F).map p ≫ (scalarLineIso k R L).hom).left := by
  rw [← Category.assoc, scalarPolynomialSourceIso,
    IsPullback.isoPullback_hom_snd]
  simpa only [MorphismProperty.Comma.comp_left, Category.assoc] using
    congrArg (fun f => f.left) (tensorPolynomialLineIso_map k R L p)

/-- The transported actual scalar puncture and the standard scalar polynomial
basic open are the same open, by their canonical Laurent comparison. -/
theorem scalarPolynomial_puncture_range :
    Set.range (pullback.snd
      ((openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫
        (polynomialAffineIso k R).hom).left ρ ≫
        (tensorPolynomialLineIso k R L).hom.left) =
      Set.range (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left := by
  let a := openInclusion (k := k) (Polynomial.X : Polynomial R)
  let c := scalarPolynomialSourceIso k R L a
  have h := (scalarPolynomialSourceIso_native k R L a).trans
    (congrArg (fun f => f.left) (scalarPunctureIso_open k R L))
  have hleft : Set.range (c.hom ≫ pullback.snd (a ≫ (polynomialAffineIso k R).hom).left ρ ≫
      (tensorPolynomialLineIso k R L).hom.left) =
        Set.range (pullback.snd (a ≫ (polynomialAffineIso k R).hom).left ρ ≫
          (tensorPolynomialLineIso k R L).hom.left) := by
    change Set.range ((pullback.snd (a ≫ (polynomialAffineIso k R).hom).left ρ ≫
      (tensorPolynomialLineIso k R L).hom.left) ∘ c.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr c.hom.surjective, Set.image_univ]
  have hright : Set.range ((scalarPunctureIso k R L).hom.left ≫
      (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left) =
        Set.range (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left := by
    change Set.range ((openInclusion (k := L)
      (Polynomial.X : Polynomial (R ⊗[k] L))).left ∘
        (scalarPunctureIso k R L).hom.left) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr
      (scalarPunctureIso k R L).hom.left.surjective, Set.image_univ]
  exact hleft.symm.trans ((congrArg (fun (f : _ ⟶ _) => Set.range f) h).trans hright)

/-- An actual tensor presentation is a presentation for the native original
scalar map, retaining its literal full closed scheme and original lift. -/
def nativeScalarPolynomialPresentation {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R))
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of ((Polynomial R) ⊗[k] L)))
    (s : Z ⟶ pullback (p ≫ (polynomialAffineIso k R).hom).left ρ)
    (y : Spec (.of ((Polynomial R) ⊗[k] L)))
    (e : OriginalEtalePresentation L
      (Spec.map (CommRingCat.ofHom (algebraMap L ((Polynomial R) ⊗[k] L))))
      (pullback.snd (p ≫ (polynomialAffineIso k R).hom).left ρ)
      (pullback.snd ((openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫
        (polynomialAffineIso k R).hom).left ρ)
      z s y) :
    OriginalEtalePresentation L (lineSite (k := L) (R := R ⊗[k] L)).hom
      ((F).map p ≫ (scalarLineIso k R L).hom).left
      (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left
      (z ≫ (tensorPolynomialLineIso k R L).hom.left)
      (s ≫ (scalarPolynomialSourceIso k R L p).inv)
      ((tensorPolynomialLineIso k R L).hom.left y) := by
  let c := scalarPolynomialSourceIso k R L p
  let i := (forgetScheme (Spec (.of L))).mapIso (tensorPolynomialLineIso k R L)
  let e' := (e.mapEtaleIso c.symm).mapAmbientIso i
  have hp : (c.hom ≫ pullback.snd (p ≫ (polynomialAffineIso k R).hom).left ρ) ≫ i.hom =
      ((F).map p ≫ (scalarLineIso k R L).hom).left := by
    change ((scalarPolynomialSourceIso k R L p).hom ≫
      pullback.snd (p ≫ (polynomialAffineIso k R).hom).left ρ) ≫
        (tensorPolynomialLineIso k R L).hom.left = _
    rw [Category.assoc]
    exact scalarPolynomialSourceIso_native k R L p
  have hb : i.inv ≫ Spec.map
      (CommRingCat.ofHom (algebraMap L ((Polynomial R) ⊗[k] L))) =
        (lineSite (k := L) (R := R ⊗[k] L)).hom :=
    MorphismProperty.Over.w (tensorPolynomialLineIso k R L).inv
  have : IsOpenImmersion (openInclusion (k := k) (Polynomial.X : Polynomial R)).left :=
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))))
  have : IsOpenImmersion
      (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left :=
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of (Polynomial (R ⊗[k] L))))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial (R ⊗[k] L)))))
  have : IsOpenImmersion ((openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫
      (polynomialAffineIso k R).hom).left :=
    inferInstanceAs (IsOpenImmersion ((openInclusion (k := k)
      (Polynomial.X : Polynomial R)).left ≫ (polynomialAffineIso k R).hom.left))
  have er := e'.withPuncture
    (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left
    (scalarPolynomial_puncture_range k R L).symm
  change OriginalEtalePresentation L
    (i.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap L ((Polynomial R) ⊗[k] L))))
    ((c.hom ≫ pullback.snd (p ≫ (polynomialAffineIso k R).hom).left ρ) ≫ i.hom)
    (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left
    (z ≫ i.hom) (s ≫ c.inv) (i.hom y) at er
  rw [hp, hb] at er
  exact er

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
