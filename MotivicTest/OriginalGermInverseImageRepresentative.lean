/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.InverseImageRepresentative
public import Lean.Util.CollectAxioms

/-! The original germ comparison uses genuine unit representatives. -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace MotivicTest.OriginalGermInverseImageRepresentative
open  _root_.AlgebraicGeometry.Scheme.SmoothSite
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
      ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.imageAdjunction b).unit.app
        ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj
            F)).hom.app
          (op (smallObject f u (compose f u M))) ≫
      ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.inverseImage b).obj
        ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj
            F)).obj.map
          ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPointLiftEquiv b
              (U.left.residueField u) q
            (smallObject f u (compose f u M))).symm (originalSmallMark f u b q h M)).op :=
  originalGermInverseImageOfFactorization_ι F f u b q h M

end MotivicTest.OriginalGermInverseImageRepresentative

open Lean in
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType in
open _root_.AlgebraicGeometry.Scheme.SmoothSite.RelativeNisnevichNeighborhood in
run_cmd do
  for name in #[
      ``MotivicTest.OriginalGermInverseImageRepresentative.actual_original_representative,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.originalGermInverseImageOfFactorization_ι,
      ``smallOriginalFiberIso_ι,
      ``original_ι_smallOriginalFiberIso_inv,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.smallFieldDiagramInjection_transport,
      ``fieldNeighborhoodInverseImageIso_marked_ι] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-germ actual unit representative: standard foundations only."
