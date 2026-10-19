/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.RightImage.RemainingLiftCases

/-!
# Actual smooth-generator right remaining lift cases

These consumers use the point closure of an original pair-incidence generic
inside the whole G,H image and the original smooth component
generator. Their image-ideal equality is supplied by the production theorem,
rather than assumed. The absent-lift Euler uses the same actual image-side
point, literal exterior ideal quotient, and original middle Y list. The
field is arbitrary and smooth objects may be disconnected; no reducedness
of either exterior or flatness of F over Y is imposed.
-/

@[expose] public section

noncomputable section

open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Hom (closedImmersion_ker_stalk_eq_top)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.RightExteriorImageComponentGeometry _root_.HomologicalComplex.ModuleLengthEuler

universe u

namespace MotivicTest.RightExteriorImageRemainingLiftCases

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (G.incidence H))

/-- The actual point closure inside the whole intermediate image. -/
abbrev imageComponent : IntegralClosedSubscheme (G.incidenceMap H).image :=
  IntegralClosedSubscheme.pointClosure ((G.incidenceMap H).toImage z.1)

/-- The actual image ideal comes from the accepted two-correspondence API;
its proof is neither repeated nor assumed as an extra premise. -/
theorem actualImageKernel :
    ((imageComponent G H z).val.subschemeι ≫ (G.incidenceMap H).imageι).ker =
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z).val :=
  ExteriorImageComponentGeometry.smoothComponent_imageKernel k G H z

/-- The actual remaining map for the original smooth component generator,
with its image-ideal equality derived rather than supplied. -/
abbrev componentRemainingMap :
    F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) ⟶ F.rightImageIncidence G H :=
  remainingToImage F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z)

/-- The actual Cartesian range identity retains the original component label. -/
theorem actualRange :
    Set.range (componentRemainingMap F G H z) =
      (F.rightImageIncidenceInclusion G H) ⁻¹'
        Set.range (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)) :=
  remainingToImage_range F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- An actual compatible exterior point yields a generic lift with that same
exterior projection; genericity is reflected by the proved closed immersion. -/
theorem actualGenericLift_preservesExterior
    (y : genericPoints (F.rightImageIncidence G H))
    (e : F.rightImageComponentExterior G H (imageComponent G H z))
    (he : F.rightImageComponentExteriorInclusion G H (imageComponent G H z) e =
      F.rightImageIncidenceInclusion G H y.1) :
    ∃ w : genericPoints (F.incidence
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)),
      componentRemainingMap F G H z w.1 = y.1 ∧
        remainingToExterior F G H (imageComponent G H z)
          (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
          (actualImageKernel G H z) w.1 = e :=
  remainingToImage_fiber_lift_generic F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z) y e he

/-- The original component has a genuine generic lift exactly on its full
exterior support, over arbitrary fields and disconnected smooth objects. -/
theorem actualGenericLift_iff (y : genericPoints (F.rightImageIncidence G H)) :
    (∃ w : genericPoints (F.incidence
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)),
      componentRemainingMap F G H z w.1 = y.1) ↔
      F.rightImageIncidenceInclusion G H y.1 ∈
        Set.range (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)) :=
  remainingToImage_exists_generic_iff F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z) y

/-- The same original fixed target point is outside the full exterior
support in the absent-lift case. No injectivity of original labels is used. -/
theorem actualNoLift_fixedPoint_outside
    (y : genericPoints (F.rightImageIncidence G H))
    (x : F.rightIntermediateImageProduct G H)
    (hp : x = F.rightImageIncidenceInclusion G H y.1)
    (hno : ¬ ∃ w : genericPoints (F.incidence
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)),
      componentRemainingMap F G H z w.1 = y.1) :
    x ∉ Set.range (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)) := by
  subst x
  exact remainingExterior_not_mem_range_of_no_genericLift F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z) y hno

/-- The literal ideal-sheaf stalk at the original fixed target point is top. -/
theorem actualNoLift_fixedPoint_kernel
    (y : genericPoints (F.rightImageIncidence G H))
    (x : F.rightIntermediateImageProduct G H)
    (hp : x = F.rightImageIncidenceInclusion G H y.1)
    (hno : ¬ ∃ w : genericPoints (F.incidence
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)),
      componentRemainingMap F G H z w.1 = y.1) :
    (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)).ker.stalk x = ⊤ :=
  closedImmersion_ker_stalk_eq_top _ (actualNoLift_fixedPoint_outside F G H z y x hp hno)

/-- No generic lift makes the actual image-exterior quotient contribution
zero for the same original remaining list, with finite homology constructed. -/
theorem actualNoLift_chainEuler_zero (y : genericPoints (F.rightImageIncidence G H))
    (hno : ¬ ∃ w : genericPoints (F.incidence
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)),
      componentRemainingMap F G H z w.1 = y.1)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y.1)))) :
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageIncidenceInclusion G H y.1)) ⧸
          (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)).ker.stalk
            (F.rightImageIncidenceInclusion G H y.1)))
      (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y.1) s))
      (remainingQuotient_finiteHomology_of_no_genericLift F G H (imageComponent G H z)
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
        (actualImageKernel G H z)
        y hno s) = 0 :=
  remainingQuotient_chainEuler_zero_of_no_genericLift F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z) y hno s

end MotivicTest.RightExteriorImageRemainingLiftCases
