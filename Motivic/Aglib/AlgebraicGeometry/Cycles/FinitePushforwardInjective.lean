/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralCycle

/-!
# Faithful cycle pushforward along closed immersions

An actual closed immersion embeds integral closed supports and has residue
degree one at every point. Its finite pushforward therefore loses no signed
cycles. No reducedness or Noetherian hypothesis is needed on either scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

namespace IntegralClosedSubscheme

/-- A closed immersion embeds the actual integral closed-subscheme basis. -/
theorem finiteImage_injective_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] :
    Function.Injective (fun V : IntegralClosedSubscheme X ↦ V.finiteImage f) := by
  intro V W h
  apply point_injective
  apply f.isClosedEmbedding.injective
  simpa only [point_finiteImage] using congrArg point h

end IntegralClosedSubscheme

namespace IntegralCycle

/-- Closed-immersion pushforward is the unweighted embedding of its support basis. -/
theorem finitePushforward_eq_mapDomain_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] :
    finitePushforward f =
      Finsupp.mapDomain.addMonoidHom (fun V : IntegralClosedSubscheme X ↦ V.finiteImage f) := by
  apply Finsupp.addHom_ext
  intro V n
  simp only [finitePushforward_single, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single, residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]

/-- Signed cycles can be compared after pushforward along an actual closed immersion. -/
theorem finitePushforward_injective_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] : Function.Injective (finitePushforward f) := by
  rw [finitePushforward_eq_mapDomain_of_isClosedImmersion]
  exact Finsupp.mapDomain_injective
    (IntegralClosedSubscheme.finiteImage_injective_of_isClosedImmersion f)

end IntegralCycle

end Motivic
