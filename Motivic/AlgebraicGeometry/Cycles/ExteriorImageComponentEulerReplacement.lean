/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageGeneric
public import Motivic.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorTargetReplacement

/-!
# Remaining-list replacement for an actual closed image exterior

At a generic point of the final whole image incidence, the original remaining
list has Artinian zero-support quotient in the original image-product stalk.
Fixed-support Koszul replacement therefore applies to the literal quotient by
an exterior component's closed-immersion kernel. Its localized generic weights
are exactly the coefficients of the restricted pushed full fundamental cycle.

The coefficient module and every prime quotient retain their original ambient
stalk scalars and the identical remaining list. No regularity of that list,
reduced exterior, purity or component-incidence Tor identification is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ExteriorImageComponentEulerReplacement

open ExteriorImageComponentGeometry LengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (F.incidenceMap G).image)

local instance sourceBaseNoetherian : IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

local instance imageProjectionFinite : IsFinite (F.leftExteriorImageSourceMap G H) :=
  F.isFinite_leftExteriorImageSourceMap k G H

local instance imageProductNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.leftExteriorImageSourceMap G H)

local instance exteriorNoetherian : IsNoetherian (exterior F G H C) :=
  isNoetherian_of_finiteType (exteriorInclusion F G H C)

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

local instance imageOpenNoetherian : IsNoetherian V.1.toScheme :=
  isNoetherian_of_finiteType V.1.ι

local instance exteriorOpenNoetherian :
    IsNoetherian (exteriorInclusion F G H C ⁻¹ᵁ V.1).toScheme :=
  isNoetherian_of_finiteType (exteriorInclusion F G H C ∣_ V.1)

/-- The original closed-exterior quotient Euler is the restricted full
fundamental-cycle coefficient sum, with the same local prime Euler factors. -/
theorem remainingEuler_replacement
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
          (exteriorInclusion F G H C).ker.stalk (V.2.fromSpec p)))
      (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
      (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) =
      ∑ᶠ q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward (exteriorInclusion F G H C ∣_ V.1)
            (fundamentalCycle (exteriorInclusion F G H C ⁻¹ᵁ V.1).toScheme))
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
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  let R := (F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)
  let M := ModuleCat.of R (R ⧸ (exteriorInclusion F G H C).ker.stalk (V.2.fromSpec p))
  let t := F.leftTargetRemainingList G H (V.2.fromSpec p) s
  refine (Koszul.fixedSupport_chainEuler_replacement M t ⊥
    (F.leftTargetRemainingList_mem_maximalIdeal G H (V.2.fromSpec p) y hp s hs) bot_le).trans ?_
  refine (F.firstStageTargetGeneric_finsum G H V p _).trans ?_
  apply finsum_congr
  intro q
  apply congrArg (fun a : ℤ => a * _)
  have hq : (F.firstStageTargetGenericEquiv G H V p).symm q =
      ⟨(genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
          (V.2.fromSpec p) q).asIdeal,
        genericStalkLocalizationPrime_mem_minimalPrimes
          (F.leftIntermediateImageProduct G H) (V.2.fromSpec p) q⟩ :=
    Subtype.ext (F.firstStageTargetGenericEquiv_symm_val G H V p q)
  rw [hq]
  exact fixedSupportGenericLength_closedImmersion_openRestriction
    (exteriorInclusion F G H C) V.1 (V.2.fromSpec p)
    (V.2.range_fromSpec.subset (Set.mem_range_self p)) q

end Motivic.ExteriorImageComponentEulerReplacement
