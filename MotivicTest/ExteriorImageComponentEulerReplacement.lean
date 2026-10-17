/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.ExteriorImageComponentEulerReplacement
public import MotivicTest.IntegralGenericFiniteImage

/-!
# The original image exterior's remaining-list Euler replacement

This consumer specializes to the original imageSupport indexed by the original
pair-incidence generic z. The quotient uses imageExteriorInclusion's literal
kernel in the original image-product stalk. The RHS uses its actual restricted
full fundamental-cycle pushforward, the identical affine point and remaining
list, and the original target-generic index. No Tor identification is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open MotivicTest.IntegralGenericFiniteImage

universe u

namespace MotivicTest.ExteriorImageComponentEulerReplacement

open LengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

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

/-- The original unreduced image exterior's quotient Euler reassembles from
its actual restricted fundamental-cycle coefficients and the same prime Eulers. -/
theorem actualClosedExteriorRemainingEuler_replacement
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
        (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
          (imageExteriorInclusion F G H z).ker.stalk (V.2.fromSpec p)))
      (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
      (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
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
              ((F.firstStageTargetGenericEquiv G H V p).symm q).2.le) :=
  Motivic.ExteriorImageComponentEulerReplacement.remainingEuler_replacement
    F G H (imageSupport F G z) V p s y hy hp hs

end MotivicTest.ExteriorImageComponentEulerReplacement
