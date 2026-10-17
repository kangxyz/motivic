/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapTransport
public import Motivic.Cohomology.A1.Basic
public import Motivic.AlgebraicGeometry.SmoothSiteInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Direct consumer of the original affine-line projection, with a transitive axiom audit. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace MotivicTest.FiniteEtaleOriginalMapRecognition
open Motivic Motivic.FiniteEtaleSite
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
local instance : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder R X).left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- For every ordinary sheaf and every degree, the constructed map is the original projection.
Neither homotopy invariance nor an inverse-image coefficient isomorphism is assumed. -/
theorem actual_a1_projection
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec R)) F n X) :
    ordinaryEdgeMap (SmoothSite.a1Projection R X).left (identityObject X)
      ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F) n
      (((SheafCohomology.presheafFunctor (nisnevichTopology X.left) n).map
        (restrictionToDirectImage F (SmoothSite.a1Projection R X))).app
          (op (identityObject X)) (cohomologyAtBaseEquiv X F n x)) =
      (SheafCohomology.presheaf (nisnevichTopology (SmoothSite.a1Cylinder R X).left)
        ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F) n).map
          (baseChangeIdentityIso (SmoothSite.a1Projection R X)).hom.op
          (cohomologyAtBaseEquiv (SmoothSite.a1Cylinder R X) F n
            (A1.projectionPullback R
              (SheafCohomology.presheaf (SmoothSite.nisnevichTopology (Spec R)) F n) X x)) :=
  ordinaryEdgeMap_atBase_originalRestriction (SmoothSite.a1Projection R X) F n x

open Lean in
run_cmd do
  for name in #[``actual_a1_projection,
      ``Motivic.FiniteEtaleSite.ordinaryEdgeMap_atBase_originalRestriction,
      ``Motivic.FiniteEtaleSite.originalRestriction_eq_transported_ordinaryEdgeMap,
      ``Motivic.FiniteEtaleSite.ordinaryEdgeMap_restrictionToDirectImage,
      ``Motivic.FiniteEtaleSite.restrictionInverseImageMap_source,
      ``Motivic.Hypercohomology.restrictionSourceIso_naturality,
      ``CategoryTheory.Adjunction.extEdge_mapExactFunctor_source] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original affine-line projection and genuine ordinary edge: standard axioms only."

end MotivicTest.FiniteEtaleOriginalMapRecognition
