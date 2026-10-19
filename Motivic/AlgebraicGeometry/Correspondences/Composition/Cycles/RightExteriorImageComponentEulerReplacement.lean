/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightFirstStageWeightedExteriorPushforward
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorTargetReplacement

/-!
# Remaining-list replacement for the actual right closed image exterior

At a generic point of the final whole right image incidence, the original Y-diagonal
list has Artinian zero-support quotient in the original right image-product stalk.
Fixed-support Koszul replacement therefore applies to the literal quotient by
an exterior component's closed-immersion kernel. Its localized generic weights
are exactly the coefficients of the restricted pushed full fundamental cycle.

The coefficient module and every prime quotient retain their original ambient
stalk scalars and the identical remaining list. No regularity of that list,
reduced exterior, purity or component-incidence Tor identification is used.
Noetherianity comes from the actual finite right exterior source map over
the finite-type exterior base; the correspondence target projection is not
assumed flat. This source-only candidate claims no compilation or acceptance.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.RightExteriorImageComponentEulerReplacement
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

open _root_.HomologicalComplex.ModuleLengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)

local instance sourceBaseNoetherian :
    IsNoetherian (pullback (F.targetProjection ≫ Y.hom) Y.hom) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  let : IsNoetherian F.scheme := isNoetherian_of_finiteType F.projection
  exact isNoetherian_of_finiteType (pullback.fst (F.targetProjection ≫ Y.hom) Y.hom)

local instance imageProjectionFinite : IsFinite (F.rightExteriorImageSourceMap G H) :=
  F.isFinite_rightExteriorImageSourceMap k G H

local instance imageProductNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.rightExteriorImageSourceMap G H)

local instance exteriorNoetherian : IsNoetherian (F.rightImageComponentExterior G H C) :=
  isNoetherian_of_finiteType (F.rightImageComponentExteriorInclusion G H C)

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

local instance imageOpenNoetherian : IsNoetherian V.1.toScheme :=
  isNoetherian_of_finiteType V.1.ι

local instance exteriorOpenNoetherian :
    IsNoetherian (F.rightImageComponentExteriorInclusion G H C ⁻¹ᵁ V.1).toScheme :=
  isNoetherian_of_finiteType (F.rightImageComponentExteriorInclusion G H C ∣_ V.1)

/-- The original closed-exterior quotient Euler is the restricted full
fundamental-cycle coefficient sum, with the same local prime Euler factors. -/
theorem remainingEuler_replacement
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
          (F.rightImageComponentExteriorInclusion G H C).ker.stalk (V.2.fromSpec p)))
      (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      ∑ᶠ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward (F.rightImageComponentExteriorInclusion G H C ∣_ V.1)
            (fundamentalCycle (F.rightImageComponentExteriorInclusion G H C ⁻¹ᵁ V.1).toScheme))
          ⟨q.1.1, q.2.mem_open V.1.isOpen
            (V.2.range_fromSpec.subset (Set.mem_range_self p))⟩ *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1
              ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).2.le) := by
  let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  let R := (F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)
  let M := ModuleCat.of R
    (R ⧸ (F.rightImageComponentExteriorInclusion G H C).ker.stalk (V.2.fromSpec p))
  let t := F.rightTargetRemainingList G H (V.2.fromSpec p) s
  refine (_root_.ChainComplex.Koszul.fixedSupport_chainEuler_replacement M t ⊥
    (F.rightTargetRemainingList_mem_maximalIdeal G H (V.2.fromSpec p) y hp s hs) bot_le).trans ?_
  refine (F.rightFirstStageTargetGeneric_finsum G H V p _).trans ?_
  apply finsum_congr
  intro q
  apply congrArg (fun a : ℤ => a * _)
  have hq : (F.rightFirstStageTargetGenericEquiv G H V p).symm q =
      ⟨(genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
          (V.2.fromSpec p) q).asIdeal,
        genericStalkLocalizationPrime_mem_minimalPrimes
          (F.rightIntermediateImageProduct G H) (V.2.fromSpec p) q⟩ :=
    Subtype.ext (F.rightFirstStageTargetGenericEquiv_symm_val G H V p q)
  rw [hq]
  exact fixedSupportGenericLength_closedImmersion_openRestriction
    (F.rightImageComponentExteriorInclusion G H C) V.1 (V.2.fromSpec p)
    (V.2.range_fromSpec.subset (Set.mem_range_self p)) q

end Motivic.RightExteriorImageComponentEulerReplacement
