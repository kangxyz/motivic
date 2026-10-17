/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImageRepresentative
public import Lean.Util.CollectAxioms

/-! The original germ comparison uses genuine unit representatives. -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace MotivicTest.OriginalGermInverseImageRepresentative
open Motivic Motivic.SmoothSite
open RelativeNisnevichNeighborhood
variable {B : Scheme.{u}} [IsAffine B] {U X : SmoothSite B}
  (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
  (f : U ⟶ X) [Etale f.left] (u : U.left) {S : Scheme.{u}}
  (b : S ⟶ X.left) (q : Spec (U.left.residueField u) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  (h : q ≫ b = U.left.fromSpecResidueField u ≫ f.left)

theorem actual_original_representative (M : NisnevichNeighborhood U u) :
    (nisnevichPointFiberCocone U u F.obj).ι.app (op M) ≫
      (originalGermInverseImageOfFactorization F f u b q h).hom =
    F.obj.map ((composeForgetIso f u).app M).hom.op ≫
      ((FiniteEtaleSite.imageAdjunction b).unit.app
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).hom.app
          (op (smallObject f u (compose f u M))) ≫
      ((FiniteEtaleSite.inverseImage b).obj
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).obj.map
          ((FiniteEtaleSite.fieldPointLiftEquiv b (U.left.residueField u) q
            (smallObject f u (compose f u M))).symm (originalSmallMark f u b q h M)).op :=
  originalGermInverseImageOfFactorization_ι F f u b q h M

end MotivicTest.OriginalGermInverseImageRepresentative

open Lean in
run_cmd do
  for name in #[
      ``MotivicTest.OriginalGermInverseImageRepresentative.actual_original_representative,
      ``Motivic.SmoothSite.originalGermInverseImageOfFactorization_ι,
      ``Motivic.SmoothSite.RelativeNisnevichNeighborhood.smallOriginalFiberIso_ι,
      ``Motivic.SmoothSite.RelativeNisnevichNeighborhood.original_ι_smallOriginalFiberIso_inv,
      ``Motivic.SmoothSite.smallFieldDiagramInjection_transport,
      ``Motivic.FiniteEtaleSite.fieldNeighborhoodInverseImageIso_marked_ι] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-germ actual unit representative: standard foundations only."
