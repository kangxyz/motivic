/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImage
public import Lean.Util.CollectAxioms

/-! Unconditional arbitrary-point inverse-image comparison for the original Nisnevich germ. -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Motivic Motivic.SmoothSite
universe u
namespace MotivicTest.OriginalGermInverseImage
variable {B : Scheme.{u}} [IsAffine B] {U X : SmoothSite B}

/-- Both endpoints are the existing objects: the original point-fiber colimit and
ordinary small-site inverse-image evaluation at the actual residue-field map. -/
def actual_original_germ_inverse_image
    (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
    (f : U ⟶ X) [Etale f.left] (u : U.left) :
    (nisnevichPointFiberCocone U u F.obj).pt ≅
      ((FiniteEtaleSite.inverseImage (X.left.fromSpecResidueField (f.left u))).obj
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).obj.obj
          (op (FiniteEtaleSite.fieldObject (U.left.residueField u)
            (Spec.map (f.left.residueFieldMap u)))) :=
  originalGermResidueInverseImageIso F f u

open Lean in
run_cmd do
  for name in #[``actual_original_germ_inverse_image,
      ``originalGermInverseImageOfFactorization, ``originalGermResidueInverseImageIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original arbitrary-point germ / genuine inverse image: standard foundations only."

end MotivicTest.OriginalGermInverseImage
