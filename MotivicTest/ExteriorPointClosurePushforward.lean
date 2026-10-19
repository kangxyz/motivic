/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.ExteriorPointClosure

/-!
# Actual simplex consumers of finite point-closure exterior pushforward

The finite ambient map may have nonreduced source or target. The support
products are the full point-closure products, and the integer factor is the
original ambient residue degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.ExteriorPointClosurePushforward

open _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward.ExteriorPointClosure

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian Y]
  (f : X ⟶ Y) [IsFinite f] (x : X) (b : Y ⟶ Spec (.of k)) (n : ℕ)

example : IsFinite (map f x b (_root_.AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example : Surjective (map f x b (_root_.AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example : IsIntegral (source f x b (_root_.AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example : IsNoetherian (target f x b (_root_.AlgebraicSimplex.smoothSiteObj k n)) := inferInstance

example :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (map f x b
        (_root_.AlgebraicSimplex.smoothSiteObj k n))
      (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (source f x b
          (_root_.AlgebraicSimplex.smoothSiteObj k n))) =
        (f.residueDegree x : ℤ) •
          _root_.AlgebraicGeometry.Scheme.fundamentalCycle (target f x b
              (_root_.AlgebraicSimplex.smoothSiteObj k n)) :=
  finitePushforward_fundamentalCycle f x b _

example (m : ℤ) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (map f x b
        (_root_.AlgebraicSimplex.smoothSiteObj k n))
      (m • _root_.AlgebraicGeometry.Scheme.fundamentalCycle (source f x b
          (_root_.AlgebraicSimplex.smoothSiteObj k n))) =
        m • ((f.residueDegree x : ℤ) •
          _root_.AlgebraicGeometry.Scheme.fundamentalCycle (target f x b
              (_root_.AlgebraicSimplex.smoothSiteObj k n))) := by
  rw [map_zsmul, finitePushforward_fundamentalCycle]

end MotivicTest.ExteriorPointClosurePushforward
