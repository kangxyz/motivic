/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.ExteriorImageRemainingCycleAttachment

/-!
# Actual smooth-component remaining cycle attachment

An original pair-incidence generic supplies both the point-closure image
support and the smooth correspondence generator. Their literal image-kernel
equality is derived by the geometric theorem. At one fixed affine point and
for one original regular middle list, the full-fundamental-cycle replacement
sum is identified with the actual pushed component-incidence Tor coefficient.

The second consumer checks the genuinely absent-support case: range exclusion
implies absence of a generic lift, and both the literal quotient Euler and the
actual pushed coefficient are zero without a regularity or kernel hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence
open Motivic.ExteriorImageComponentGeometry Motivic.ExteriorImageRemainingCycleAttachment
open Motivic.LengthEuler

universe u

namespace MotivicTest.ExteriorImageRemainingCycleAttachment

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

/-- The actual integral image support of this original pair-incidence label. -/
abbrev imageComponent :=
  IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)

/-- The original smooth generator's actual remaining closed immersion, with
its image-kernel equality supplied by geometry rather than a new hypothesis. -/
abbrev componentRemainingMap :
    (F.smoothIncidenceComponentGenerator k G z).incidence H ⟶ F.leftImageIncidence G H :=
  remainingToImage F G H (imageComponent F G z)
    (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z)

local instance imageProductNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  ExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

local instance imageExteriorNoetherian : IsNoetherian (exterior F G H (imageComponent F G z)) :=
  ExteriorImageComponentEulerReplacement.exteriorNoetherian F G H (imageComponent F G z)

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

local instance imageOpenNoetherian : IsNoetherian V.1.toScheme :=
  ExteriorImageComponentEulerReplacement.imageOpenNoetherian F G H V

local instance imageExteriorOpenNoetherian :
    IsNoetherian (exteriorInclusion F G H (imageComponent F G z) ⁻¹ᵁ V.1).toScheme :=
  ExteriorImageComponentEulerReplacement.exteriorOpenNoetherian F G H (imageComponent F G z) V

/-- For the actual original smooth component, the preceding whole-exterior
replacement sum equals its pushed remaining incidence Tor coefficient. The
same original affine point and list serve every term, even when no lift exists. -/
theorem actualRemainingPushforwardCoefficient_replacement
    (y : genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y.1)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y.1 y.2 hp s hker
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (componentRemainingMap F G H z)
        (IntegralCycle.ofGenericCoefficients
          ((F.smoothIncidenceComponentGenerator k G z).incidence H)
          ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H))) y.1 =
      ∑ᶠ q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward
            (exteriorInclusion F G H (imageComponent F G z) ∣_ V.1)
            (fundamentalCycle
              (exteriorInclusion F G H (imageComponent F G z) ⁻¹ᵁ V.1).toScheme))
          ⟨q.1.1, q.2.mem_open V.1.isOpen
            (V.2.range_fromSpec.subset (Set.mem_range_self p))⟩ *
          chainEuler (Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                ((F.firstStageTargetGenericEquiv G H V p).symm q).1))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              ((F.firstStageTargetGenericEquiv G H V p).symm q).1
              ((F.firstStageTargetGenericEquiv G H V p).symm q).2.le) := by
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y.1 y.2 hp s hker
  exact (remainingQuotientEuler_eq_finitePushforward_coefficient
    F G H (imageComponent F G z) (F.smoothIncidenceComponentGenerator k G z)
    (smoothComponent_imageKernel k F G z) y (V.2.fromSpec p) hp s hsreg hker).symm.trans
      (ExteriorImageComponentEulerReplacement.remainingEuler_replacement
        F G H (imageComponent F G z) V p s y.1 y.2 hp hker)

omit V p in
/-- Exclusion from the actual exterior range gives both zero terms, with no
regularity or kernel presentation of the original middle list assumed. -/
theorem actualOutsideExterior_chainEuler_and_pushforward_zero
    (y : genericPoints (F.leftImageIncidence G H))
    (hout : F.leftImageIncidenceInclusion G H y.1 ∉
      Set.range (exteriorInclusion F G H (imageComponent F G z)))
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y.1)))) :
    let hno : ¬ ∃ w : genericPoints ((F.smoothIncidenceComponentGenerator k G z).incidence H),
        componentRemainingMap F G H z w.1 = y.1 :=
      fun hw => hout ((remainingToImage_exists_generic_iff F G H (imageComponent F G z)
        (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z) y).mp hw)
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
        y hno s) = 0 ∧
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (componentRemainingMap F G H z)
          (IntegralCycle.ofGenericCoefficients
            ((F.smoothIncidenceComponentGenerator k G z).incidence H)
            ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H))) y.1 = 0 := by
  dsimp only
  have hno : ¬ ∃ w : genericPoints ((F.smoothIncidenceComponentGenerator k G z).incidence H),
      componentRemainingMap F G H z w.1 = y.1 :=
    fun hw => hout ((remainingToImage_exists_generic_iff F G H (imageComponent F G z)
      (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z) y).mp hw)
  exact ⟨remainingQuotient_chainEuler_zero_of_no_genericLift F G H (imageComponent F G z)
    (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z) y hno s,
    remainingToImage_TorCoefficient_zero_of_no_genericLift F G H (imageComponent F G z)
      (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z) y.1 hno⟩

end MotivicTest.ExteriorImageRemainingCycleAttachment
