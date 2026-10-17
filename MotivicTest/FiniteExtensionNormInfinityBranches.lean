module

import Motivic.KTheory.MilnorK.FiniteExtensionNormInfinityBranches

/-! Regression checks for the original-field infinity norm and branch formula. -/

open Motivic.KTheory.MilnorK

universe u
variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

example (n : ℕ) (x : K E n) :
    infinityTwistNorm k E n x =
      map n (RatFunc.inversion k).toRingHom (finiteExtensionNorm (RatFunc k) E n x) :=
  infinityTwistNorm_eq k E n x

example (n : ℕ) (x : K E (n + 1)) :
    InfinityResidue.residue k n (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      infinityBranchResidueSum k E n x :=
  infinityResidue_finiteExtensionNorm k E n x
