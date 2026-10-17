/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermRelativeNeighborhood
public import Lean.Util.CollectAxioms

/-! Direct original-fiber comparison without a residue-field-isomorphism assumption. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
open SmoothSite SmoothSite.RelativeNisnevichNeighborhood
universe u
namespace MotivicTest.OriginalGermRelativeNeighborhood
variable {S : Scheme.{u}} [IsAffine S] {U X : SmoothSite S}
  (f : U ⟶ X) [Etale f.left] (u : U.left)
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The right side is the original, not newly substituted, point fiber. -/
def actual_original_fiber : colimit ((forget f u).op ⋙ F) ≅
    (nisnevichPointFiberCocone U u F).pt := originalFiberIso f u F

/-- The actual representative maps agree under this comparison. -/
theorem actual_representative (M : NisnevichNeighborhood U u) :
    colimit.ι ((forget f u).op ⋙ F) (op (compose f u M)) ≫
        (actual_original_fiber f u F).hom =
      F.map ((composeForgetIso f u).app M).inv.op ≫
        (nisnevichPointFiberCocone U u F).ι.app (op M) :=
  originalFiberIso_ι f u F M

open Lean in
run_cmd do
  for name in #[``actual_original_fiber, ``actual_representative,
      ``composeFunctor_initial, ``originalFiberIso, ``originalFiberIso_ι] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual relative neighborhood / original germ comparison: standard foundations only."

end MotivicTest.OriginalGermRelativeNeighborhood
