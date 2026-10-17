/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.ExteriorImageRemainingTorAttachment
public import MotivicTest.IntegralGenericFiniteImage

/-!
# The original imageSupport quotient and its remaining incidence coefficient

The first consumer keeps the original affine point and middle list, the actual
imageSupport exterior ideal, and the original generator incidence coefficient.
The second attaches that coefficient to the preceding full-fundamental-cycle
Euler replacement at precisely the same fixed point. The source incidence
point maps to the specified y by an explicit geometric hypothesis. There is
no assumed equality of scalar actions, list images, Euler values or cycles.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence
open MotivicTest.IntegralGenericFiniteImage Motivic.ExteriorImageComponentGeometry
open Motivic.LengthEuler

universe u

namespace MotivicTest.ExteriorImageRemainingTorAttachment

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))
  (P : FiniteCorrespondenceGenerator X.hom Z.hom)
  (hC : ((imageSupport F G z).val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)
  (w : genericPoints (P.incidence H))

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance actualImageProductNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  Motivic.ExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

local instance actualImageExteriorNoetherian : IsNoetherian (imageExterior F G H z) :=
  Motivic.ExteriorImageComponentEulerReplacement.exteriorNoetherian F G H (imageSupport F G z)

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

local instance actualImageOpenNoetherian : IsNoetherian V.1.toScheme :=
  Motivic.ExteriorImageComponentEulerReplacement.imageOpenNoetherian F G H V

local instance actualImageExteriorOpenNoetherian :
    IsNoetherian (imageExteriorInclusion F G H z ⁻¹ᵁ V.1).toScheme :=
  Motivic.ExteriorImageComponentEulerReplacement.exteriorOpenNoetherian
    F G H (imageSupport F G z) V

/-- The same original list at the fixed affine point computes the actual
remaining incidence coefficient through the full exterior ideal quotient. -/
theorem actualClosedExteriorRemainingEuler_eq_incidenceTorCoefficient
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hwy : remainingToImage F G H (imageSupport F G z) P hC w.1 = y)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
        (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
          (imageExteriorInclusion F G H z).ker.stalk (V.2.fromSpec p)))
      (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
      (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
      P.incidenceTorCoefficient H w :=
  ExteriorImageRemainingTorAttachment.remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
    F G H (imageSupport F G z) P hC w (V.2.fromSpec p) y hy hp hwy s hsreg hker

/-- At that same fixed point the preceding replacement sum is attached to
the original incidence Tor coefficient, retaining the same original list. -/
theorem actualRemainingTorCoefficient_replacement
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hwy : remainingToImage F G H (imageSupport F G z) P hC w.1 = y)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
    P.incidenceTorCoefficient H w =
      ∑ᶠ q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward (imageExteriorInclusion F G H z ∣_ V.1)
            (fundamentalCycle (imageExteriorInclusion F G H z ⁻¹ᵁ V.1).toScheme))
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
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
  exact (actualClosedExteriorRemainingEuler_eq_incidenceTorCoefficient
    F G H z P hC w V p y hy hp hwy s hsreg hker).symm.trans
      (Motivic.ExteriorImageComponentEulerReplacement.remainingEuler_replacement
        F G H (imageSupport F G z) V p s y hy hp hker)

end MotivicTest.ExteriorImageRemainingTorAttachment
