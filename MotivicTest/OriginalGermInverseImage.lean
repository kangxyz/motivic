/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.InverseImage
public import Lean.Util.CollectAxioms

/-! Unconditional arbitrary-point inverse-image comparison for the original Nisnevich germ. -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry  _root_.AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace MotivicTest.OriginalGermInverseImage
variable {B : Scheme.{u}} [IsAffine B] {U X : SmoothSite B}

/-- Both endpoints are the existing objects: the original point-fiber colimit and
ordinary small-site inverse-image evaluation at the actual residue-field map. -/
def actualOriginalGermInverseImage
    (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
    (f : U ⟶ X) [Etale f.left] (u : U.left) :
    (nisnevichPointFiberCocone U u F.obj).pt ≅
      ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.inverseImage
          (X.left.fromSpecResidueField (f.left u))).obj
        ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj
            F)).obj.obj
          (op (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldObject
              (U.left.residueField u)
            (Spec.map (f.left.residueFieldMap u)))) :=
  originalGermResidueInverseImageIso F f u

open Lean in
run_cmd do
  for name in #[``actualOriginalGermInverseImage,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.originalGermInverseImageOfFactorization,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.originalGermResidueInverseImageIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original arbitrary-point germ / genuine inverse image: standard foundations only."

end MotivicTest.OriginalGermInverseImage
