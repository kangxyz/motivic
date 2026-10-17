/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.CoproductUnitAutomorphism

/-! # The literal coordinate unit on an actual open affine-line source

The actual source map is retained, rather than replaced by its open image. The
coordinate difference is a unit on its product with the full boundary scheme,
including nonreduced boundaries, and extends by identity on an arbitrary disjoint
component.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)

/-- Disjointness of the actual source and boundary images excludes the coordinate graph
from their product. No immersion hypothesis is needed for this geometric statement. -/
theorem coordinateGraph_disjoint_sourceProduct {V : Scheme.{u}}
    (q : V ⟶ Spec (.of R[X]))
    (h : Disjoint (Set.range q) (Set.range (boundaryCoordinateMap R B z))) :
    Disjoint (Set.range (boundaryGraphTarget (boundaryLineProjection R)
      (boundaryCoordinateMap R B z)))
      (Set.range (boundaryProductMap (boundaryLineProjection R) q
        (boundaryCoordinateMap R B z))) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨b, rfl⟩ ⟨a, ha⟩
  have he := congrArg (fun v => (pullback.fst (boundaryLineProjection R)
    (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)) v) ha
  have hleft : (pullback.fst (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
        (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z) a) =
      q (pullback.fst (q ≫ boundaryLineProjection R)
        (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) a) := by
    change (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z) ≫
      pullback.fst _ _) a = _
    rw [boundaryProductMap, pullback.lift_fst]
    rfl
  have hright : (pullback.fst (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
      (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z) b) =
        boundaryCoordinateMap R B z b := by
    change (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z) ≫
      pullback.fst _ _) b = _
    rw [boundaryGraphTarget, pullback.lift_fst]
  exact Set.disjoint_left.mp h
    ⟨pullback.fst (q ≫ boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) a, rfl⟩
    ⟨b, (hleft.symm.trans (he.trans hright)).symm⟩

/-- The exact coordinate endomorphism is invertible on the product of an actual
open affine-line source and the full original boundary. -/
theorem boundaryCoordinateEndomorphism_affineSource_isIso {V : Scheme.{u}}
    (q : V ⟶ Spec (.of R[X])) [IsOpenImmersion q]
    (h : Disjoint (Set.range q) (Set.range (boundaryCoordinateMap R B z))) :
    IsIso (boundaryCoordinateEndomorphism R B z
      (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z))) :=
  boundaryCoordinateEndomorphism_isIso R B z _
    (coordinateGraph_disjoint_sourceProduct R B z q h)

/-- One actual coproduct unit is identity on an arbitrary component and is literally
the coordinate endomorphism on the product of the original source and boundary. -/
theorem exists_affineSourceBoundaryUnit {V : Scheme.{u}}
    (q : V ⟶ Spec (.of R[X])) [IsOpenImmersion q]
    (h : Disjoint (Set.range q) (Set.range (boundaryCoordinateMap R B z)))
    (D : Scheme.{u}) :
    let Z := pullback (q ≫ boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)
    ∃ E : SheafOfModules.unit (D ⨿ Z).ringCatSheaf ≅
        SheafOfModules.unit (D ⨿ Z).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom = 𝟙 _ ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom ≫
        (restrictUnitIso _).hom = (restrictUnitIso _).hom ≫
          boundaryCoordinateEndomorphism R B z
            (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z)) := by
  let := boundaryCoordinateEndomorphism_affineSource_isIso R B z q h
  exact exists_coprod_unitAutomorphism _ _
    (asIso (boundaryCoordinateEndomorphism R B z
      (boundaryProductMap (boundaryLineProjection R) q (boundaryCoordinateMap R B z))))

end AlgebraicGeometry.Scheme.Hom
