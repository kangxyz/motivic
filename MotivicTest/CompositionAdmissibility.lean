/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Admissibility
public import Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralCycle

/-!
# Consumers of actual finite-image admissibility

The finite projection applies to every integral incidence support, not only
components and not only reduced incidence. Component dominance remains explicit
where it is used to construct a generator. Finite pushforward uses exactly the
same integral image; no derived intersection cycle is silently chosen.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CompositionAdmissibility
open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme IntegralCycle)

example {W T X : Scheme.{u}} (a : W ⟶ T) (p : T ⟶ X)
    [IsFinite (a ≫ p)] [IsSeparated p] [LocallyOfFiniteType p] :
    IsFinite (a.imageι ≫ p) := _root_.AlgebraicGeometry.Scheme.Hom.isFinite_image_projection a p

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
variable (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
variable [IsSeparated h] [LocallyOfFiniteType h]
variable (C : IntegralClosedSubscheme (A.incidence B))

example : IsFinite
    (correspondenceProjection f h (C.finiteImage (A.incidenceMap B)).val) :=
  A.isFinite_incidenceImage_projection B C

example : Set.range
    (correspondenceProjection f h (C.finiteImage (A.incidenceMap B)).val) =
      Set.range (C.val.subschemeι ≫ A.incidenceSource B) :=
  A.range_incidenceImage_projection B C

example (hC : Function.Surjective (C.val.subschemeι ≫ A.incidenceFst B)) :
    (A.incidenceImageGeneratorOfSurjective B C hC).val =
      (C.finiteImage (A.incidenceMap B)).val := rfl

example (n : ℤ) :
    IntegralCycle.finitePushforward (A.incidenceMap B) (Finsupp.single C n) =
      Finsupp.single (C.finiteImage (A.incidenceMap B))
        (n * (C.imageDegree (A.incidenceMap B) : ℤ)) :=
  IntegralCycle.finitePushforward_single_imageDegree _ _ _

example (hA : GeneralizingMap (A.incidenceFst B))
    (x : genericPoints (A.incidence B)) :
    (A.incidenceComponentImageGenerator B hA x).val =
      ((IntegralClosedSubscheme.pointClosure x.val).finiteImage (A.incidenceMap B)).val := rfl

end MotivicTest.CompositionAdmissibility
