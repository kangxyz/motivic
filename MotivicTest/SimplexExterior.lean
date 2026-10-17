/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexExterior

/-!
# Consumers of actual signed simplex exterior correspondences

These statements retain arbitrary fields, disconnected smooth sources and
targets, actual geometric supports, and negative integer multiplicities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SimplexExterior

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (V : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℕ)

example : GeometricallyIntegral (AlgebraicSimplex.structureMap k n) := inferInstance

example : IsIntegral (V.exteriorIdentitySupport (AlgebraicSimplex.smoothSiteObj k n)) :=
  inferInstance

example : IsClosedImmersion (V.exteriorIdentityInclusion (AlgebraicSimplex.smoothSiteObj k n)) :=
  inferInstance

example : Set.range (V.exteriorIdentitySource (AlgebraicSimplex.smoothSiteObj k n)) ∈
    irreducibleComponents (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left :=
  V.exteriorIdentitySource_range_mem _

example :
    FiniteCorrespondence.simplexExterior (X := X) (Y := Y) n (Finsupp.single V (-3)) =
      Finsupp.single (V.exteriorIdentityGenerator (AlgebraicSimplex.smoothSiteObj k n)) (-3) :=
  FiniteCorrespondence.simplexExterior_single n V (-3)

example :
    FiniteCorrespondence.toIntegralCycle
      (V.exteriorIdentityGenerator (AlgebraicSimplex.smoothSiteObj k n)).cycle =
      IntegralCycle.finitePushforward
        (V.exteriorIdentityInclusion (AlgebraicSimplex.smoothSiteObj k n))
        (fundamentalCycle (V.exteriorIdentitySupport (AlgebraicSimplex.smoothSiteObj k n))) :=
  V.toIntegralCycle_exteriorIdentityGenerator_cycle _

example {A B : Cor k} (α β : A ⟶ B) :
    Cor.simplexExterior n (α - 2 • β) =
      Cor.simplexExterior n α - 2 • Cor.simplexExterior n β := by
  simp

example {A B : Cor k} : Cor.simplexExterior n (0 : A ⟶ B) = 0 :=
  map_zero _

example {A B : Cor k} (α β : A ⟶ B) :
    Cor.simplexExterior n (α + β) = Cor.simplexExterior n α + Cor.simplexExterior n β := by
  simp

end MotivicTest.SimplexExterior
