/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityComponentPushforward

/-! # Actual simplex consumers of the incidence-component exterior pushforward -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityComponentPushforward

open WholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom) (n : ℕ)
  (x : genericPoints (A.incidence B))

example :
    ExteriorPointClosurePushforward.target (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom) (AlgebraicSimplex.smoothSiteObj k n) ≅
      (A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySupport
        (AlgebraicSimplex.smoothSiteObj k n) :=
  A.exteriorIncidenceComponentTargetIso B _ x

example :
    componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
        (AlgebraicSimplex.smoothSiteObj k n).hom x ≫
        A.exteriorIncidenceAmbientMap B (AlgebraicSimplex.smoothSiteObj k n) =
      A.exteriorIncidenceComponentAmbientMap B (AlgebraicSimplex.smoothSiteObj k n) x :=
  A.exteriorIncidenceComponentAmbientMap_factorization B _ x

example :
    IntegralCycle.finitePushforward
        (A.exteriorIncidenceAmbientMap B (AlgebraicSimplex.smoothSiteObj k n))
        (IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
            (AlgebraicSimplex.smoothSiteObj k n).hom x)
          (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
            (AlgebraicSimplex.smoothSiteObj k n).hom x))) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          ((A.smoothIncidenceComponentGenerator k B x).exteriorIdentityGenerator
            (AlgebraicSimplex.smoothSiteObj k n)).cycle :=
  A.exteriorIncidence_finitePushforward_componentFundamentalCycle B _ x

example (m : ℤ) :
    IntegralCycle.finitePushforward
        (A.exteriorIncidenceComponentAmbientMap B (AlgebraicSimplex.smoothSiteObj k n) x)
        (m • fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
          (AlgebraicSimplex.smoothSiteObj k n).hom x)) =
      m • (((A.incidenceMap B).residueDegree x.1 : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          ((A.smoothIncidenceComponentGenerator k B x).exteriorIdentityGenerator
            (AlgebraicSimplex.smoothSiteObj k n)).cycle) := by
  rw [map_zsmul, A.exteriorIncidenceComponentAmbientMap_fundamentalCycle B _ x]

end MotivicTest.ExteriorIdentityComponentPushforward
