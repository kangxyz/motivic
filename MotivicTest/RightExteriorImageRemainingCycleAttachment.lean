/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightExteriorImageRemainingCycleAttachment

/-!
# Actual smooth-component right remaining cycle attachment

An original G,H incidence generic determines its actual image point closure
and smooth correspondence generator. Their literal image-kernel equality is
derived from the public two-correspondence theorem. Over an arbitrary field,
the full right exterior quotient at a fixed point computes the actual pushed
F,component incidence Tor coefficient, with or without a generic lift.

The same original Y list and image-side stalk scalars are retained. The
absent-support consumer checks both genuine zero terms without regularity
or a diagonal-kernel hypothesis. No exterior is reduced and no injectivity
of the original G,H component labels, perfectness, connectedness, or flatness
of F over Y is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence
open Motivic.RightExteriorImageComponentGeometry
open Motivic.RightExteriorImageRemainingCycleAttachment Motivic.LengthEuler

universe u

namespace MotivicTest.RightExteriorImageRemainingCycleAttachment

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (G.incidence H))

/-- The actual integral image support for this original pair-incidence label. -/
abbrev imageComponent : IntegralClosedSubscheme (G.incidenceMap H).image :=
  IntegralClosedSubscheme.pointClosure ((G.incidenceMap H).toImage z.1)

/-- The original smooth component has the required literal ideal by geometry,
not by an additional hypothesis on the Euler or Tor expression. -/
theorem actualImageKernel :
    ((imageComponent G H z).val.subschemeι ≫ (G.incidenceMap H).imageι).ker =
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z).val :=
  ExteriorImageComponentGeometry.smoothComponent_imageKernel
    (X := Y) (Y := Z) (Z := W) k G H z

/-- The actual remaining map uses the original component and derived kernel. -/
abbrev componentRemainingMap :
    F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) ⟶ F.rightImageIncidence G H :=
  remainingToImage F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance sourceNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance actualIncidenceNoetherian :
    IsNoetherian (F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z)) :=
  isNoetherian_of_finiteType (F.incidenceSource
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z))

local instance imageProductNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  RightExteriorImageRemainingTorAttachment.imageProductNoetherian F G H

/-- At an arbitrary fixed target point, the actual component's full quotient
Euler is its true finite pushed incidence Tor coefficient, including no lift. -/
theorem actualRemainingQuotientEuler_eq_finitePushforward_coefficient
    (y : genericPoints (F.rightImageIncidence G H))
    (x : F.rightIntermediateImageProduct G H)
    (hp : x = F.rightImageIncidenceInclusion G H y.1)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H x)))
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H x)) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk (F.rightImageMiddlePair G H x) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H x y.1 y.2 hp s hker
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk x)
        (((F.rightIntermediateImageProduct G H).presheaf.stalk x) ⧸
          (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)).ker.stalk x))
      (F.rightTargetRemainingList G H x s))
      (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (componentRemainingMap F G H z)
          (IntegralCycle.ofGenericCoefficients
            (F.incidence (G.smoothIncidenceComponentGenerator
              (X := Y) (Y := Z) (Z := W) k H z))
            (F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
              (X := Y) (Y := Z) (Z := W) k H z)))) y.1 :=
  remainingQuotientEuler_eq_finitePushforward_coefficient F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z) y x hp s hsreg hker

/-- A genuine lift has precisely its original Tor contribution; uniqueness
comes only from this remaining closed immersion and the residue degree is one. -/
theorem actualGenericLift_pushforward_coefficient
    (w : genericPoints (F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z)))
    (y : F.rightImageIncidence G H)
    (hwy : componentRemainingMap F G H z w.1 = y) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (componentRemainingMap F G H z)
        (IntegralCycle.ofGenericCoefficients
          (F.incidence (G.smoothIncidenceComponentGenerator
            (X := Y) (Y := Z) (Z := W) k H z))
          (F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
            (X := Y) (Y := Z) (Z := W) k H z)))) y =
      F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
        (X := Y) (Y := Z) (Z := W) k H z) w :=
  remainingToImage_TorCoefficient_of_genericLift F G H (imageComponent G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z) w y hwy

/-- Actual exterior-range exclusion gives both zero terms for the same Y
list, without assuming regularity or any kernel presentation of that list. -/
theorem actualOutsideExterior_chainEuler_and_pushforward_zero
    (y : genericPoints (F.rightImageIncidence G H))
    (hout : F.rightImageIncidenceInclusion G H y.1 ∉
      Set.range (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y.1)))) :
    let hno : ¬ ∃ w : genericPoints (F.incidence (G.smoothIncidenceComponentGenerator
        (X := Y) (Y := Z) (Z := W) k H z)), componentRemainingMap F G H z w.1 = y.1 :=
      fun hw => hout ((remainingToImage_exists_generic_iff F G H (imageComponent G H z)
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
        (actualImageKernel G H z) y).mp hw)
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageIncidenceInclusion G H y.1)) ⧸
          (F.rightImageComponentExteriorInclusion G H (imageComponent G H z)).ker.stalk
            (F.rightImageIncidenceInclusion G H y.1)))
      (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y.1) s))
      (remainingQuotient_finiteHomology_of_no_genericLift F G H (imageComponent G H z)
        (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
        (actualImageKernel G H z) y hno s) = 0 ∧
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (componentRemainingMap F G H z)
          (IntegralCycle.ofGenericCoefficients
            (F.incidence (G.smoothIncidenceComponentGenerator
              (X := Y) (Y := Z) (Z := W) k H z))
            (F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
              (X := Y) (Y := Z) (Z := W) k H z)))) y.1 = 0 := by
  dsimp only
  have hno : ¬ ∃ w : genericPoints (F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z)), componentRemainingMap F G H z w.1 = y.1 :=
    fun hw => hout ((remainingToImage_exists_generic_iff F G H (imageComponent G H z)
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
      (actualImageKernel G H z) y).mp hw)
  exact ⟨remainingQuotient_chainEuler_zero_of_no_genericLift F G H (imageComponent G H z)
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
      (actualImageKernel G H z) y hno s,
    remainingToImage_TorCoefficient_zero_of_no_genericLift F G H (imageComponent G H z)
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
      (actualImageKernel G H z) y.1 hno⟩

end MotivicTest.RightExteriorImageRemainingCycleAttachment
