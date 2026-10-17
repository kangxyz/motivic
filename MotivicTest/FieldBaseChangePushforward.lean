/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangePushforward

/-!
# Arbitrary-field incidence-component pushforward consumers

The field extension is arbitrary. Smooth objects can be disconnected and both
whole pullbacks can split or acquire nilpotents. These consumers impose no
normality on the image and no separability or finite-type condition on the
extension. The equality is of full cycles and retains the old residue degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FieldBaseChangePushforward

universe u

namespace MotivicTest.FieldBaseChangePushforward

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (x : genericPoints (A.incidence B))

/-- The map really is finite with no restriction on the ground-field extension. -/
example : IsFinite (FieldBaseChangePushforward.map φ A B x) := inferInstance

/-- Finite projections onto the new smooth scheme give whole-source Noetherianity. -/
example : IsNoetherian (source φ A B x) := inferInstance

/-- The whole possibly nonnormal, nonreduced, disconnected target is Noetherian. -/
example : IsNoetherian (target φ A B x) := inferInstance

/-- The actual point-closure square remains Cartesian before taking cycles. -/
theorem actualPointClosureSquare :
    IsPullback
      (pullback.fst (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)))
      (FieldBaseChangePushforward.map φ A B x)
      (IntegralClosedSubscheme.pointClosureMap (A.incidenceMap B) x.1)
      (pullback.fst (originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ))) :=
  FieldBaseChangePushforward.isPullback φ A B x

/-- Every new source component maps to an actual new target component. -/
theorem actualGenericPreservation (w : genericPoints (source φ A B x)) :
    FieldBaseChangePushforward.map φ A B x w.1 ∈ genericPoints (target φ A B x) :=
  map_generic φ A B x w

/-- The whole-cycle equality retains the old incidence residue degree. -/
theorem originalDegreeWholeCycle :
    IntegralCycle.finitePushforward (FieldBaseChangePushforward.map φ A B x)
      (fundamentalCycle (source φ A B x)) =
        ((A.incidenceMap B).residueDegree x.1 : ℤ) •
          fundamentalCycle (target φ A B x) :=
  finitePushforward_fundamentalCycle φ A B x

/-- Every branch above each target generic occurs, including branch collisions. -/
theorem allBranchDegreeLength (y : genericPoints (target φ A B x)) :
    IntegralExteriorDegreeLength.actualGenericFiberDegreeLengthSum
      (FieldBaseChangePushforward.map φ A B x) y.1 =
        ((A.incidenceMap B).residueDegree x.1 : ℤ) * (genericMultiplicity y : ℤ) :=
  IntegralExteriorDegreeLength.actualGenericFiberDegreeLengthSum_eq
    (A.incidenceMap B) x.1 (FieldBaseChangePushforward.isPullback φ A B x) y
    (target_generic_projection φ A B x y)

/-- Nongeneric vanishing is independently available for point-extensional gluing. -/
theorem offGenericCoefficient (y : target φ A B x)
    (hy : y ∉ genericPoints (target φ A B x)) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (FieldBaseChangePushforward.map φ A B x)
        (fundamentalCycle (source φ A B x))) y = 0 :=
  pushforward_eq_zero_of_not_generic φ A B x y hy

open Lean in
run_cmd do
  for name in #[``actualPointClosureSquare, ``actualGenericPreservation,
      ``originalDegreeWholeCycle, ``allBranchDegreeLength, ``offGenericCoefficient,
      ``FieldBaseChangePushforward.originalTargetProjection_isFinite,
      ``FieldBaseChangePushforward.sourceProjection_isPullback,
      ``FieldBaseChangePushforward.targetProjection_isPullback,
      ``FieldBaseChangePushforward.sourceProjection_generic,
      ``FieldBaseChangePushforward.target_generic_projection,
      ``FieldBaseChangePushforward.source_isNoetherian,
      ``FieldBaseChangePushforward.target_isNoetherian] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Arbitrary-field finite pushforward uses only standard foundations."

end MotivicTest.FieldBaseChangePushforward
