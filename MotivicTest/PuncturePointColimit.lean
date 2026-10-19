/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Puncture.PointColimit
public import Motivic.Cohomology.A1.LocalVanishing.Puncture.OrdinaryComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Actual original cohomology and actual point-fiber consumers of the zero-section square. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.PuncturePointColimit
open Motivic _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}) (n : ℕ)
local instance : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder R X).left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The conclusion is zero for the genuine higher-direct-image point fiber.
Punctured comparison and injectivity are still explicitly independent geometric inputs. -/
theorem actual_pointFiber_isZero
    (hbase : IsZero (colimit (pointedBaseValues R Φ
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n))))
    [IsIso (colim.map (pointedProjection R Φ
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) (pointedPuncture R j Φ)))]
    [Mono (colim.map (pointedCylinderRestriction R j Φ
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n)))] :
    IsZero (Φ.sheafFiber.obj
      (((directImage (SmoothSite.a1Projection R X).left).rightDerived n).obj
        ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat.{u + 1}).obj F))) :=
  (pointedCylinder_colimit_isZero R j Φ
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) hbase).of_iso
    (pointedCylinderColimitFiberIso R X Φ F n).symm

open Lean in
run_cmd do
  for name in #[``actual_pointFiber_isZero,
      ``Motivic.FiniteEtaleSite.pointedCylinderRestriction_zeroSection_colimit,
      ``Motivic.FiniteEtaleSite.pointedCylinderRestriction_colimit_eq_zero,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.a1BaseChangeIso_naturality,
      ``Motivic.FiniteEtaleSite.pointedPunctureCylinderColimitFiberIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual pointed puncture, original maps and genuine point fiber: standard axioms only."

end MotivicTest.PuncturePointColimit
