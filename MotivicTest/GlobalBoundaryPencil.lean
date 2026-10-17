/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Motivic.Aglib.AlgebraicGeometry.GlobalBoundaryPencil

/-! Direct consumers for the actual global pencil and its canonical endpoints. -/

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open GlobalBoundaryPencil

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

example {X : Scheme.{u}} (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback (endpoint X 0)).map (familyMap L a b) ≫
      (pullbackUnitIso (endpoint X 0)).hom =
    (sectionPullbackIso (endpoint X 0) (parameterSpace X ↘ X)
      (endpoint_projection X 0)).hom.app L.val ≫ a := familyMap_zero L a b

example {X : Scheme.{u}} (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback (endpoint X 1)).map (familyMap L a b) ≫
      (pullbackUnitIso (endpoint X 1)).hom =
    (sectionPullbackIso (endpoint X 1) (parameterSpace X ↘ X)
      (endpoint_projection X 1)).hom.app L.val ≫ b := familyMap_one L a b

-- These declarations quantify over arbitrary schemes and boundary maps.
-- In particular no reducedness, integrality, or boundary pointwise replacement occurs.
#check familyMap_boundary
#print axioms pullback_unitMul
#print axioms familyMap_zero
#print axioms familyMap_one
#print axioms familyMap_boundary
#print axioms familyMap_boundary_zero_isEmpty
#print axioms family_finite_flat_on_open
