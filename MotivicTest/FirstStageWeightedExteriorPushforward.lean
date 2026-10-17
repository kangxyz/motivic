/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FirstStageWeightedExteriorPushforward

/-!
# Arbitrary-field consumers of the actual weighted exterior pushforward

These exact API checks use the existing original component exterior and the
existing image-component exterior, without a MotivicTest alias chain. All geometric
instances are derived from the actual SmoothSite generators. The per-component
global equality and the endpoint retain whole fundamental cycles, all original
labels and their signed Tor weights, and the original incidence residue degree.

Prepared source-only; no compilation or acceptance is asserted here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.WholeFiberTorExteriorDecomposition Motivic.ExteriorImageComponentGeometry
open scoped BigOperators

universe u

namespace MotivicTest.FirstStageWeightedExteriorPushforward

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance consumer_sourceNoetherian :
    IsNoetherian (F.leftIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType
    (pullback.fst (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom))

local instance consumer_sourceBaseNoetherian :
    IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

local instance consumer_imageProjectionFinite : IsFinite (F.leftExteriorImageSourceMap G H) :=
  F.isFinite_leftExteriorImageSourceMap k G H

local instance consumer_imageNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.leftExteriorImageSourceMap G H)

local instance consumer_sourceComponentNoetherian (z : genericPoints (F.incidence G)) :
    IsNoetherian (componentExterior (F.incidenceTarget G ≫ Z.hom)
      (H.projection ≫ Z.hom) z) :=
  isNoetherian_of_finiteType
    (componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z)

local instance consumer_imageComponentNoetherian
    (C : IntegralClosedSubscheme (F.incidenceMap G).image) :
    IsNoetherian (exterior F G H C) :=
  isNoetherian_of_finiteType (exteriorInclusion F G H C)

local instance consumer_componentMapFinite (z : genericPoints (F.incidence G)) :
    IsFinite (F.firstStageComponentExteriorMap G H z) :=
  F.firstStageComponentExteriorMap_isFinite G H z

/-- The actual component map preserves generics without a supplied comparison hypothesis. -/
example (z : genericPoints (F.incidence G))
    (w : genericPoints (componentExterior (F.incidenceTarget G ≫ Z.hom)
      (H.projection ≫ Z.hom) z)) :
    F.firstStageComponentExteriorMap G H z w.1 ∈
      genericPoints (exterior F G H
        (IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1))) :=
  F.firstStageComponentExteriorMap_mem_genericPoints G H z w

/-- Global equality of the two full exterior cycles uses the original ambient degree. -/
example (z : genericPoints (F.incidence G)) :
    IntegralCycle.finitePushforward (F.firstStageComponentExteriorMap G H z)
        (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
          (H.projection ≫ Z.hom) z)) =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) •
        fundamentalCycle (ExteriorImageComponentGeometry.exterior F G H
          (IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1))) :=
  F.firstStageComponentExteriorMap_finitePushforward_fundamentalCycle G H z

/-- The endpoint consumes the existing original exterior cycle, with all signed labels. -/
example :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (F.firstStageOriginalExteriorCycle G H) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward
            (ExteriorImageComponentGeometry.exteriorInclusion F G H
              (IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)))
            (fundamentalCycle (ExteriorImageComponentGeometry.exterior F G H
              (IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)))) :=
  F.firstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum G H

end MotivicTest.FirstStageWeightedExteriorPushforward
