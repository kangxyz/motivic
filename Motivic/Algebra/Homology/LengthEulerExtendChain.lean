/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEulerExtend

/-!
# Placing a nonnegative chain complex in a higher degree

Extension along the translation `n ↦ n + q` is the actual zero extension of
a nonnegative chain complex. Its homology length Euler characteristic is
multiplied by `(-1)^q`. No finite-length hypothesis on the terms is required.
-/

@[expose] public section

universe u v

namespace Motivic.LengthEuler

/-- The shape embedding placing a nonnegative chain complex in degree `q`. -/
def chainPlacement (q : ℕ) : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) where
  f n := n + q
  injective_f := fun _ _ h => Nat.add_right_cancel h
  rel := by
    intro i j h
    change j + 1 = i at h
    change (j + q) + 1 = i + q
    omega

instance instChainPlacementIsRelIff (q : ℕ) : (chainPlacement q).IsRelIff where
  rel' := by
    intro i j h
    change (j + q) + 1 = i + q at h
    change j + 1 = i
    omega

variable {R : Type u} [Ring R]

/-- Placing an actual complex in degree `q` multiplies its Euler length by `(-1)^q`. -/
theorem chainEuler_extend_placement (K : ChainComplex (ModuleCat.{v} R) ℕ)
    (q : ℕ) (hK : FiniteHomology K) :
    chainEuler (K.extend (chainPlacement q)) (hK.extend (chainPlacement q)) =
      (-1 : ℤ) ^ q * chainEuler K hK := by
  change homologyEuler (K.extend (chainPlacement q)) (fun i => (-1 : ℤ) ^ i)
    (hK.extend (chainPlacement q)) = _
  rw [homologyEuler_extend (chainPlacement q) _ hK]
  change (∑ᶠ i, (-1 : ℤ) ^ (i + q) * integerLength (K.homology i) (hK.finite_length i)) =
    (-1 : ℤ) ^ q * ∑ᶠ i, (-1 : ℤ) ^ i * integerLength (K.homology i) (hK.finite_length i)
  rw [mul_finsum]
  apply finsum_congr
  intro i
  rw [pow_add]
  ring

end Motivic.LengthEuler
