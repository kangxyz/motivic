/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermSmallRelativeNeighborhood
public import Lean.Util.CollectAxioms

/-! Original germs computed in actual finite-type small-site neighborhoods. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
open SmoothSite SmoothSite.RelativeNisnevichNeighborhood
universe u
namespace MotivicTest.OriginalGermSmallRelativeNeighborhood
variable {S : Scheme.{u}} [IsAffine S] {U X : SmoothSite S}
  (f : U ⟶ X) [Etale f.left] (u : U.left)
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The literal small-site field-valued diagram computes the existing original point fiber. -/
def actual_small_original_fiber : colimit ((smallForget f u).op ⋙ F) ≅
    (nisnevichPointFiberCocone U u F).pt := smallOriginalFiberIso f u F

open Lean in
run_cmd do
  for name in #[``actual_small_original_fiber, ``toSmall_initial, ``smallOriginalFiberIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual small-site / original germ colimit: standard foundations only."

end MotivicTest.OriginalGermSmallRelativeNeighborhood
