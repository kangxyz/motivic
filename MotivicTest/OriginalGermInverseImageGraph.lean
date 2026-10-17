/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImageGraph
public import Lean.Util.CollectAxioms

/-! Original point-fiber pullback is the actual inverse-image field restriction. -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace MotivicTest.OriginalGermInverseImageGraph
open Motivic Motivic.SmoothSite
open RelativeNisnevichNeighborhood NisnevichNeighborhood
variable {B : Scheme.{u}} [IsAffine B] {V U X : SmoothSite B}
  (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
  (f : U ⟶ X) [Etale f.left] (g : V ⟶ U) [Etale g.left] (v : V.left)
  {S : Scheme.{u}} (b : S ⟶ X.left)
  (q : Spec (U.left.residueField (g.left v)) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  (h : q ≫ b = U.left.fromSpecResidueField (g.left v) ≫ f.left)
local instance : Etale (g ≫ f).left :=
  inferInstanceAs (Etale (g.left ≫ f.left))

theorem actual_original_pullback :
    originalGermPullback.{u, u + 1} F.obj g v ≫
      (originalGermInverseImageOfFactorization F (g ≫ f) v b
        (Spec.map (g.left.residueFieldMap v) ≫ q)
        (originalSourceFactorization f g v b q h)).hom =
    (originalGermInverseImageOfFactorization F f (g.left v) b q h).hom ≫
      ((FiniteEtaleSite.inverseImage b).obj
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).obj.map
          (originalResidueFieldObjectMap g v q).op :=
  originalGermInverseImageOfFactorization_pullback F f g v b q h

open Lean in
run_cmd do
  for name in #[``actual_original_pullback,
      ``originalGermInverseImageOfFactorization_pullback,
      ``originalSmallMark_lift_naturality, ``originalSmallPullbackRefinement_underlying] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-germ graph comparison: standard foundations only."

end MotivicTest.OriginalGermInverseImageGraph
