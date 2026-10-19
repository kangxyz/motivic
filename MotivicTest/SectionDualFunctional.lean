module
import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.DualFunctional

/-! # Direct tests for original section dualization and boundary avoidance -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u

variable {X W : Scheme.{u}} (f : W ⟶ X) (L : LineBundle X)
  (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)

example : Hom.pullbackToUnit (sectionDualFunctional X L s) f =
    pulledSectionDualFunctional f L s :=
  sectionDualFunctional_pullback f L s

example [IsIso (pullbackSectionMap f s)] :
    IsIso (Hom.pullbackToUnit (sectionDualFunctional X L s) f) :=
  sectionDualFunctional_pullback_isIso f L s

example [IsIso (pullbackSectionMap f s)] :
    IsEmpty (pullback (C := Scheme.{u}) f (Hom.zeroInclusion (sectionDualFunctional X L s))) :=
  sectionDualFunctional_boundary_isEmpty f L s
