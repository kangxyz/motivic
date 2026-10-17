/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightExteriorImageRemainingTorAttachment
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageRemainingLiftCases

/-!
# Actual right image components and their original remaining Tor coefficients

Over an arbitrary field, an ORIGINAL G,H incidence generic determines the
literal point closure of its actual image and the actual smooth component
generator. Its image-ideal equality is proved, not supplied as a Tor-shaped
hypothesis. At a fixed affine point and a generic remaining-incidence lift,
the full exterior quotient Euler computes F's original incidence Tor.

The second consumer chooses one actual remaining Y-diagonal list at the
fixed target point and applies the theorem to precisely that list. Neither
consumer assumes a globally existing lift or a flat correspondence projection.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence
open Motivic.RightExteriorImageComponentGeometry Motivic.LengthEuler
open Motivic.RightExteriorImageRemainingTorAttachment
  (remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint)

universe u

namespace MotivicTest.RightExteriorImageRemainingTorAttachment

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (G.incidence H))

/-- The original generic label determines its actual support inside the whole image. -/
abbrev imageSupport : IntegralClosedSubscheme (G.incidenceMap H).image :=
  IntegralClosedSubscheme.pointClosure ((G.incidenceMap H).toImage z.1)

/-- The actual smooth component generator has exactly the required original image ideal. -/
theorem actualImageKernel :
    ((imageSupport G H z).val.subschemeι ≫ (G.incidenceMap H).imageι).ker =
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z).val :=
  ExteriorImageComponentGeometry.smoothComponent_imageKernel (X := Y) (Y := Z) (Z := W) k G H z

/-- The map uses the actual image support and the original component generator. -/
abbrev actualRemainingToImage :
    F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) ⟶ F.rightImageIncidence G H :=
  remainingToImage F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance actualImageProductNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  Motivic.RightExteriorImageRemainingTorAttachment.imageProductNoetherian F G H

variable (w : genericPoints (F.incidence (G.smoothIncidenceComponentGenerator
  (X := Y) (Y := Z) (Z := W) k H z)))

/-- The actual three scalar maps are surjective, without assuming F is flat over Y. -/
theorem actualScalarMaps_surjective :
    let C := imageSupport G H z
    let P := G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z
    let e := remainingToExterior F G H C P (actualImageKernel G H z) w.1
    Function.Surjective ((F.rightImageComponentExteriorInclusion G H C).stalkMap e).hom ∧
      Function.Surjective ((exteriorIso F G H C P (actualImageKernel G H z)).hom.stalkMap e).hom ∧
      Function.Surjective
        (remainingExteriorCoefficientStalkMap F G H C P (actualImageKernel G H z) w.1).hom :=
  Motivic.RightExteriorImageRemainingTorAttachment.remainingExterior_scalarMaps_surjective
    F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z)
      (actualImageKernel G H z) w.1

/-- An arbitrary original regular list at the fixed affine target computes the
original F,P Tor coefficient through the literal full exterior ideal quotient. -/
theorem actualClosedExteriorRemainingEuler_eq_incidenceTorCoefficient
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hwy : actualRemainingToImage F G H z w.1 = y)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
          (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)).ker.stalk
            (V.2.fromSpec p)))
      (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
      (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
      F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
        (X := Y) (Y := Z) (Z := W) k H z) w :=
  remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
    F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z)
      (actualImageKernel G H z) w (V.2.fromSpec p) y hy hp hwy s hsreg hker

/-- Smoothness supplies an original list at the specified image-side point;
the same list computes Tor when the actual generic remaining lift is supplied. -/
theorem exists_actualRemainingList_computes_incidenceTorCoefficient
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hwy : actualRemainingToImage F G H z w.1 = y) :
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))),
      IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))) s ∧
      ∃ hker : (pullback.diagonal Y.hom).ker.stalk
          (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y)) = Ideal.ofList s,
        letI := F.rightTargetRemainingList_support_isArtinian G H
          (F.rightImageIncidenceInclusion G H y) y hy rfl s hker
        chainEuler (Koszul.coefficientComplex
          (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk
              (F.rightImageIncidenceInclusion G H y))
            (((F.rightIntermediateImageProduct G H).presheaf.stalk
                (F.rightImageIncidenceInclusion G H y)) ⧸
              (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)).ker.stalk
                (F.rightImageIncidenceInclusion G H y)))
          (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y) s))
          (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
          F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
            (X := Y) (Y := Z) (Z := W) k H z) w := by
  obtain ⟨s, hsreg, hker⟩ := F.exists_rightImageIncidenceRemainingList G H y
  refine ⟨s, hsreg, hker, ?_⟩
  exact remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
    F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z)
      (actualImageKernel G H z) w (F.rightImageIncidenceInclusion G H y) y hy rfl hwy s hsreg hker

end MotivicTest.RightExteriorImageRemainingTorAttachment
