/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.UnitAutomorphism

/-! # The actual prescribed unit for the fixed-source psi pencil -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- On the full fixed-source boundary, one actual unit is identity at infinity and
exactly the coordinate difference at Z. No rational function or unit premise is supplied. -/
theorem exists_fixedOpenBoundaryUnit
    (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    (U : (Spec (.of R[X])).Opens)
    (hU : Disjoint (U : Set (Spec (.of R[X]))) (Set.range (boundaryCoordinateMap R B z)))
    {D : Scheme.{u}} (d : D ⟶ Spec (.of R)) :
    let A := pullback (U.ι ≫ boundaryLineProjection R) d
    let Z := pullback (U.ι ≫ boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)
    ∃ E : SheafOfModules.unit (A ⨿ Z).ringCatSheaf ≅
        SheafOfModules.unit (A ⨿ Z).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : A ⟶ A ⨿ Z)).map E.hom = 𝟙 _ ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : Z ⟶ A ⨿ Z)).map E.hom ≫
        (restrictUnitIso _).hom = (restrictUnitIso _).hom ≫
          boundaryCoordinateEndomorphism R B z
            (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z)) := by
  let := boundaryCoordinateEndomorphism_open_isIso R B z U hU
  exact exists_coprod_unitAutomorphism _ _
    (asIso (boundaryCoordinateEndomorphism R B z
      (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z))))

end AlgebraicGeometry.Scheme.Hom
