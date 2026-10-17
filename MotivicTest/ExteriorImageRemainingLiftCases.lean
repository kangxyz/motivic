/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageRemainingLiftCases

/-!
# Actual smooth-generator remaining lift cases

These consumers use the point closure of an original pair-incidence generic
inside the whole intermediate image and the original smooth component
generator. Their image-ideal equality is supplied by the production theorem,
rather than assumed. The absent-lift Euler uses the same actual image-side
point, literal exterior ideal quotient, and original middle list.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.ExteriorImageComponentGeometry Motivic.LengthEuler

universe u

namespace MotivicTest.ExteriorImageRemainingLiftCases

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

/-- The actual point closure inside the whole intermediate image. -/
abbrev imageComponent :=
  IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)

/-- The actual remaining map for the original smooth component generator,
with its image-ideal equality derived rather than supplied. -/
abbrev componentRemainingMap :
    (F.smoothIncidenceComponentGenerator k G z).incidence H ⟶ F.leftImageIncidence G H :=
  remainingToImage F G H (imageComponent F G z)
    (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z)

/-- The original component has a genuine generic lift exactly on its full
exterior support, over arbitrary fields and disconnected smooth objects. -/
theorem actualGenericLift_iff (y : genericPoints (F.leftImageIncidence G H)) :
    (∃ w : genericPoints ((F.smoothIncidenceComponentGenerator k G z).incidence H),
      componentRemainingMap F G H z w.1 = y.1) ↔
      F.leftImageIncidenceInclusion G H y.1 ∈
        Set.range (exteriorInclusion F G H (imageComponent F G z)) :=
  remainingToImage_exists_generic_iff F G H (imageComponent F G z)
    (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z) y

/-- No generic lift makes the actual image-exterior quotient contribution
zero for the same original remaining list, with finite homology constructed. -/
theorem actualNoLift_chainEuler_zero (y : genericPoints (F.leftImageIncidence G H))
    (hno : ¬ ∃ w : genericPoints ((F.smoothIncidenceComponentGenerator k G z).incidence H),
      componentRemainingMap F G H z w.1 = y.1)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y.1)))) :
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (F.leftImageIncidenceInclusion G H y.1))
        (((F.leftIntermediateImageProduct G H).presheaf.stalk
          (F.leftImageIncidenceInclusion G H y.1)) ⧸
          (exteriorInclusion F G H (imageComponent F G z)).ker.stalk
            (F.leftImageIncidenceInclusion G H y.1)))
      (F.leftTargetRemainingList G H (F.leftImageIncidenceInclusion G H y.1) s))
      (remainingQuotient_finiteHomology_of_no_genericLift F G H (imageComponent F G z)
        (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z)
        y hno s) = 0 :=
  remainingQuotient_chainEuler_zero_of_no_genericLift F G H (imageComponent F G z)
    (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z) y hno s

end MotivicTest.ExteriorImageRemainingLiftCases
