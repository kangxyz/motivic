/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightExteriorImageComponentEulerReplacement

/-!
# The actual right image exterior's remaining-list Euler replacement

Over an arbitrary field, an ORIGINAL G,H incidence generic supplies its actual
image point-closure. The quotient uses the full right exterior inclusion's
literal kernel in the original image-product stalk. Its replacement sums the
actual restricted full fundamental-cycle coefficients against the SAME prime
quotient Eulers, at the same affine point and with the same remaining Y list.

The consumer assumes only that the list generates the literal diagonal kernel,
not regularity, perfectness, connectedness, reducedness or a Tor identification.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.RightExteriorImageComponentEulerReplacement

open LengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (G.incidence H))

/-- The actual support remembers the ORIGINAL G,H generic label. -/
abbrev imageSupport : IntegralClosedSubscheme (G.incidenceMap H).image :=
  IntegralClosedSubscheme.pointClosure ((G.incidenceMap H).toImage z.1)

local instance actualImageProductNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  Motivic.RightExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

local instance actualImageExteriorNoetherian :
    IsNoetherian (F.rightImageComponentExterior G H (imageSupport G H z)) :=
  Motivic.RightExteriorImageComponentEulerReplacement.exteriorNoetherian F G H (imageSupport G H z)

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

local instance actualImageOpenNoetherian : IsNoetherian V.1.toScheme :=
  Motivic.RightExteriorImageComponentEulerReplacement.imageOpenNoetherian F G H V

local instance actualImageExteriorOpenNoetherian :
    IsNoetherian
      (F.rightImageComponentExteriorInclusion G H (imageSupport G H z) ⁻¹ᵁ V.1).toScheme :=
  Motivic.RightExteriorImageComponentEulerReplacement.exteriorOpenNoetherian
    F G H (imageSupport G H z) V

/-- The original unreduced image exterior's quotient Euler reassembles from
its actual restricted fundamental-cycle coefficients and the same prime Eulers. -/
theorem actualClosedExteriorRemainingEuler_replacement
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
          (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)).ker.stalk
            (V.2.fromSpec p)))
      (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
      (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
      ∑ᶠ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward
            (F.rightImageComponentExteriorInclusion G H (imageSupport G H z) ∣_ V.1)
            (fundamentalCycle
              (F.rightImageComponentExteriorInclusion G H (imageSupport G H z) ⁻¹ᵁ V.1).toScheme))
          ⟨q.1.1, q.2.mem_open V.1.isOpen
            (V.2.range_fromSpec.subset (Set.mem_range_self p))⟩ *
          chainEuler (Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1
              ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).2.le) :=
  Motivic.RightExteriorImageComponentEulerReplacement.remainingEuler_replacement
    F G H (imageSupport G H z) V p s y hy hp hs

end MotivicTest.RightExteriorImageComponentEulerReplacement
