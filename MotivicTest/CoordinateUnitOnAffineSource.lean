module

import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnAffineSource

/-! # The exact boundary unit on the original affine-line source -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.Modules Scheme.Hom

universe u

example (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    {V : Scheme.{u}} (q : V ⟶ Spec (.of R[X])) [IsOpenImmersion q]
    (h : Disjoint (Set.range q) (Set.range (boundaryCoordinateMap R B z))) :
    IsIso (boundaryCoordinateEndomorphism R B z
      (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z))) :=
  boundaryCoordinateEndomorphism_affineSource_isIso R B z q h

example (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    {V : Scheme.{u}} (q : V ⟶ Spec (.of R[X])) [IsOpenImmersion q]
    (h : Disjoint (Set.range q) (Set.range (boundaryCoordinateMap R B z)))
    {D : Scheme.{u}} (d : D ⟶ Spec (.of R)) :
    let A := pullback (q ≫ boundaryLineProjection R) d
    let Z := pullback (q ≫ boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)
    ∃ E : SheafOfModules.unit (A ⨿ Z).ringCatSheaf ≅
        SheafOfModules.unit (A ⨿ Z).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : A ⟶ A ⨿ Z)).map E.hom = 𝟙 _ ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : Z ⟶ A ⨿ Z)).map E.hom ≫
        (restrictUnitIso _).hom = (restrictUnitIso _).hom ≫
          boundaryCoordinateEndomorphism R B z
            (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z)) :=
  exists_affineSourceBoundaryUnit R B z q h (pullback (q ≫ boundaryLineProjection R) d)
