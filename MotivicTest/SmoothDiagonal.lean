/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.Smooth
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of regular kernels of smooth scheme diagonal stalks

The general consumer has arbitrary source and base schemes, without a
separatedness or Noetherian assumption. Identity morphisms also exercise the
result over arbitrary schemes and the nonreduced affine base `Spec (ZMod 4)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.SmoothDiagonal

/-- The literal diagonal stalk kernel of an arbitrary smooth scheme morphism is regular. -/
theorem arbitraryBase {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ rs : List ((pullback f f).presheaf.stalk (pullback.diagonal f x)),
      IsRegular ((pullback f f).presheaf.stalk (pullback.diagonal f x)) rs ∧
        RingHom.ker ((pullback.diagonal f).stalkMap x).hom = Ideal.ofList rs :=
  Diagonal.exists_regular_kernel_of_smooth f x

/-- Identity morphisms need no regularity assumption on their source scheme. -/
theorem identity (X : Scheme.{u}) (x : X) :
    ∃ rs : List ((pullback (𝟙 X) (𝟙 X)).presheaf.stalk (pullback.diagonal (𝟙 X) x)),
      IsRegular ((pullback (𝟙 X) (𝟙 X)).presheaf.stalk
        (pullback.diagonal (𝟙 X) x)) rs ∧
        RingHom.ker ((pullback.diagonal (𝟙 X)).stalkMap x).hom = Ideal.ofList rs :=
  Diagonal.exists_regular_kernel_of_smooth (𝟙 X) x

/-- A nonreduced coefficient scheme is a valid base for the geometric theorem. -/
theorem nonreducedBase (x : Spec (CommRingCat.of (ZMod 4))) :
    let X := Spec (CommRingCat.of (ZMod 4))
    ∃ rs : List ((pullback (𝟙 X) (𝟙 X)).presheaf.stalk (pullback.diagonal (𝟙 X) x)),
      IsRegular ((pullback (𝟙 X) (𝟙 X)).presheaf.stalk
        (pullback.diagonal (𝟙 X) x)) rs ∧
        RingHom.ker ((pullback.diagonal (𝟙 X)).stalkMap x).hom = Ideal.ofList rs :=
  identity _ x

end Motivic.MotivicTest.SmoothDiagonal
