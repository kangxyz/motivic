/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyH1GenericOpenLift
public import Lean.Util.CollectAxioms

/-! # Generic affine-open lifting of an actual H¹ representative -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

open Motivic Motivic.SheafCohomology

namespace MotivicTest.SheafCohomologyH1GenericOpenLift

variable {S : Scheme.{u}} [IsAffine S]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

example
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (X : SmoothSite S) [IsIntegral X.left]
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1 X) :
    ∃ (s : (cokernel (Injective.ι F)).obj.obj (op X)),
      injectiveSectionBoundary (SmoothSite.nisnevichTopology S) F X s = x ∧
    ∃ (A : SmoothSite S) (j : A ⟶ X), IsAffine A.left ∧ IsOpenImmersion j.left ∧
      genericPoint X.left ∈ Set.range j.left ∧
    ∃ l : (Injective.under F).obj.obj (op A),
      (cokernel.π (Injective.ι F)).hom.app (op A) l =
        (cokernel (Injective.ι F)).obj.map j.op s :=
  exists_generic_affine_open_lift_of_h_one F X x

open Lean in
run_cmd do
  let name := ``exists_generic_affine_open_lift_of_h_one
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Generic-open lifting of actual ordinary H¹ uses only standard Lean foundations."

end MotivicTest.SheafCohomologyH1GenericOpenLift
