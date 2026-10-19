/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.Ambient
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineMiddleScalars

/-!
# The actual middle-diagonal ambient Tor comparison

For commutative algebras A,B,C over any field k, the literal quotient map
from (A tensor_k B) tensor_k (B tensor_k C) to
(A tensor_k B) tensor_B (B tensor_k C) identifies the two middle actions.
Its two adjacent factor maps are flat because the remaining outer algebras
are flat over the field. The generic ambient Tor theorem therefore applies
to arbitrary modules on the adjacent factors, without any extra hypothesis.

The output is an isomorphism over the full four-factor ambient ring. The
three-factor ring here is the literal balanced tensor ring; its checked
isomorphism to (A tensor_k B) tensor_k C is not treated as a type equality.
This file does not identify support-ring stalks or claim a geometric
coefficient comparison beyond these algebraic modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace ModuleCat.TorComparison
open _root_.Algebra.TensorProduct _root_.AlgebraicGeometry.Scheme.Products

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The left map induced by the actual ambient quotient is the actual first
adjacent coordinate inclusion into the balanced triple ring. -/
theorem ambientMiddle_leftMap :
    MixedBase.leftMap k (A ⊗[k] B) (B ⊗[k] C)
      (MiddleDiagonal.tripleRing k A B C) (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (MiddleDiagonal.leftMap k A B C).toRingHom :=
  congrArg AlgHom.toRingHom (MiddleDiagonal.quotientMap_comp_left k A B C)

/-- The right map induced by the actual ambient quotient is the actual second
adjacent coordinate inclusion into the balanced triple ring. -/
theorem ambientMiddle_rightMap :
    MixedBase.rightMap k (A ⊗[k] B) (B ⊗[k] C)
      (MiddleDiagonal.tripleRing k A B C) (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (MiddleDiagonal.rightMap k A B C).toRingHom :=
  congrArg AlgHom.toRingHom (MiddleDiagonal.quotientMap_comp_right k A B C)

/-- All-degree reduction to the actual middle-diagonal quotient for arbitrary
modules over the adjacent factors, over every field and with no support-flatness.
The ambient quotient itself is not assumed flat. -/
def ambientMiddleTorIso
    (M : ModuleCat.{u} (A ⊗[k] B)) (N : ModuleCat.{u} (B ⊗[k] C)) (n : ℕ) :
    ((Tor (ModuleCat (MiddleDiagonal.ambientRing k A B C)) n).obj
      (ExteriorModule.obj k (A ⊗[k] B) (B ⊗[k] C) M N)).obj
        ((ModuleCat.restrictScalars (MiddleDiagonal.quotientMap k A B C).toRingHom).obj
          (ModuleCat.of (MiddleDiagonal.tripleRing k A B C)
            (MiddleDiagonal.tripleRing k A B C))) ≅
      (ModuleCat.restrictScalars (MiddleDiagonal.quotientMap k A B C).toRingHom).obj
        (((Tor (ModuleCat (MiddleDiagonal.tripleRing k A B C)) n).obj
          ((ModuleCat.extendScalars (MiddleDiagonal.leftMap k A B C).toRingHom).obj M)).obj
            ((ModuleCat.extendScalars (MiddleDiagonal.rightMap k A B C).toRingHom).obj N)) := by
  have hleft : (MixedBase.leftMap k (A ⊗[k] B) (B ⊗[k] C)
      (MiddleDiagonal.tripleRing k A B C)
      (MiddleDiagonal.quotientMap k A B C).toRingHom).Flat := by
    rw [ambientMiddle_leftMap]
    exact MiddleDiagonal.leftMap_flat k A B C
  have hright : (MixedBase.rightMap k (A ⊗[k] B) (B ⊗[k] C)
      (MiddleDiagonal.tripleRing k A B C)
      (MiddleDiagonal.quotientMap k A B C).toRingHom).Flat := by
    rw [ambientMiddle_rightMap]
    exact MiddleDiagonal.rightMap_flat k A B C
  simpa only [ambientMiddle_leftMap, ambientMiddle_rightMap] using
    ambientTorIso (MiddleDiagonal.quotientMap k A B C).toRingHom hleft hright M N n

end ModuleCat.TorComparison
