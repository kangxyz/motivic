/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ProjectiveMap
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FixedOpenBoundaryUnit

/-! # The fixed punctured source and whole relative psi boundary

Only the original base principal open is imposed on the punctured affine line.
The boundary unit is exactly identity on the full missing neighborhood and the
original coordinate difference on the entire zero component.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) (r : R)

/-- Exactly Gm over the chosen original base principal open. -/
def fixedPsiSource : (Spec (.of (Polynomial R))).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X * Polynomial.C r)

lemma fixedPsiSource_eq : fixedPsiSource R r =
    PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) ⊓
      (Scheme.Hom.boundaryLineProjection R ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
  rw [fixedPsiSource, PrimeSpectrum.basicOpen_mul]
  rw [Scheme.Hom.boundaryLineProjection, SpecMap_preimage_basicOpen]
  rfl

instance : IsAffine (fixedPsiSource R r).toScheme :=
  IsAffineOpen.Spec_basicOpen (Polynomial.X * Polynomial.C r)

lemma fixedPsiSource_disjoint_zero :
    Disjoint (fixedPsiSource R r : Set _)
      (Set.range (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0))) := by
  change Disjoint (fixedPsiSource R r : Set _)
    (Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))
  rw [range_affine_zero, fixedPsiSource_eq]
  exact Set.disjoint_left.mpr (fun _ hx hn ↦ hn hx.1)

/-- The structural projection from the fixed punctured source to `Spec R`. -/
abbrev fixedPsiProjection := (fixedPsiSource R r).ι ≫ Scheme.Hom.boundaryLineProjection R
/-- The projective line over the fixed punctured source, presented as a pullback. -/
abbrev fixedPsiAmbient := pullback (fixedPsiProjection R r) (ProjectiveSpace.toSpec R
  (ULift.{u} (Fin 2)))
/-- The pullback of the missing neighborhood boundary to the fixed punctured source. -/
abbrev fixedPsiMissing := pullback (fixedPsiProjection R r)
  (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
/-- The pullback of the original zero component to the fixed punctured source. -/
abbrev fixedPsiZero := pullback (fixedPsiProjection R r)
  (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
    Scheme.Hom.boundaryLineProjection R)
/-- The coproduct of the missing and zero boundary components over the fixed punctured source. -/
abbrev fixedPsiBoundary := fixedPsiMissing R V r ⨿ fixedPsiZero R r

/-- The actual entire-boundary automorphism supplied by the original coordinate. -/
def fixedPsiBoundaryUnit : SheafOfModules.unit (fixedPsiBoundary R V r).ringCatSheaf ≅
    SheafOfModules.unit (fixedPsiBoundary R V r).ringCatSheaf :=
  Classical.choose (Scheme.Hom.exists_fixedOpenBoundaryUnit R R (Polynomial.evalRingHom 0)
    (fixedPsiSource R r) (fixedPsiSource_disjoint_zero R r)
    (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R _))

lemma fixedPsiBoundaryUnit_missing :
    (restrictFunctor (coprod.inl : fixedPsiMissing R V r ⟶ fixedPsiBoundary R V r)).map
      (fixedPsiBoundaryUnit R V r).hom = 𝟙 _ :=
  (Classical.choose_spec (Scheme.Hom.exists_fixedOpenBoundaryUnit R R
    (Polynomial.evalRingHom 0) (fixedPsiSource R r) (fixedPsiSource_disjoint_zero R r)
    (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R _))).1

lemma fixedPsiBoundaryUnit_zero :
    (restrictFunctor (coprod.inr : fixedPsiZero R r ⟶ fixedPsiBoundary R V r)).map
        (fixedPsiBoundaryUnit R V r).hom ≫ (restrictUnitIso _).hom =
      (restrictUnitIso _).hom ≫ Scheme.Hom.boundaryCoordinateEndomorphism R R
        (Polynomial.evalRingHom 0)
        (Scheme.Hom.boundaryProductMap (Scheme.Hom.boundaryLineProjection R)
          (fixedPsiSource R r).ι
          (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0))) :=
  (Classical.choose_spec (Scheme.Hom.exists_fixedOpenBoundaryUnit R R
    (Polynomial.evalRingHom 0) (fixedPsiSource R r) (fixedPsiSource_disjoint_zero R r)
    (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R _))).2

/-- Only reassociation of the literal structural map identifies this product with
its already checked native projective presentation. -/
def fixedPsiAmbientIso : fixedPsiAmbient R r ≅
    neighborhoodGraphAmbient R (fixedPsiSource R r) :=
  pullback.congrHom (by simp only [fixedPsiProjection, neighborhoodProjection,
    neighborhoodInclusion, Category.assoc, chart_toSpec,
    Scheme.Hom.boundaryLineProjection]) rfl

/-- Identify the fixed ambient pullback with the projective line over the source section ring. -/
def fixedPsiProjectiveIso : fixedPsiAmbient R r ≅
    ProjectiveSpace Γ((fixedPsiSource R r).toScheme, ⊤) (ULift.{u} (Fin 2)) :=
  fixedPsiAmbientIso R r ≪≫ neighborhoodProjectiveIso R (fixedPsiSource R r)

end AlgebraicGeometry.RelativeProjectiveLine
