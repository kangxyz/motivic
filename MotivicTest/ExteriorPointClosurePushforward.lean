/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorPointClosurePushforward

/-!
# Actual simplex consumers of finite point-closure exterior pushforward

The finite ambient map may have nonreduced source or target. The support
products are the full point-closure products, and the integer factor is the
original ambient residue degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorPointClosurePushforward

open Motivic.ExteriorPointClosurePushforward

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian Y]
  (f : X ⟶ Y) [IsFinite f] (x : X) (b : Y ⟶ Spec (.of k)) (n : ℕ)

example : IsFinite (map f x b (AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example : Surjective (map f x b (AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example : IsIntegral (source f x b (AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example : IsNoetherian (target f x b (AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example :
    IntegralCycle.finitePushforward (map f x b (AlgebraicSimplex.smoothSiteObj k n))
      (fundamentalCycle (source f x b (AlgebraicSimplex.smoothSiteObj k n))) =
        (f.residueDegree x : ℤ) •
          fundamentalCycle (target f x b (AlgebraicSimplex.smoothSiteObj k n)) :=
  finitePushforward_fundamentalCycle f x b _

example (m : ℤ) :
    IntegralCycle.finitePushforward (map f x b (AlgebraicSimplex.smoothSiteObj k n))
      (m • fundamentalCycle (source f x b (AlgebraicSimplex.smoothSiteObj k n))) =
        m • ((f.residueDegree x : ℤ) •
          fundamentalCycle (target f x b (AlgebraicSimplex.smoothSiteObj k n))) := by
  rw [map_zsmul, ExteriorPointClosurePushforward.finitePushforward_fundamentalCycle]

end MotivicTest.ExteriorPointClosurePushforward
