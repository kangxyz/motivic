/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.SmoothKoszul

/-!
# Consumers of actual smooth diagonal stalk resolutions

The first consumer exposes the literal stalk-map scalar action on the source
stalk. The others retain completely arbitrary coefficient modules in the Tor
comparison and finite-degree vanishing theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.SmoothDiagonalKoszul

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X)

/-- The resolution targets the source stalk with its actual diagonal scalar action. -/
theorem actualSourceStalk :
    let A := (pullback f f).presheaf.stalk (pullback.diagonal f x)
    let := ((pullback.diagonal f).stalkMap x).hom.toAlgebra
    Nonempty (ProjectiveResolution (ModuleCat.of A (X.presheaf.stalk x))) :=
  ⟨Diagonal.projectiveResolution f x⟩

/-- The Tor comparison retains arbitrary coefficients without an extra regularity hypothesis. -/
def arbitraryCoefficient (M : ModuleCat (Diagonal.ambientStalk f x)) (n : ℕ) :
    ((Tor (ModuleCat (Diagonal.ambientStalk f x)) n).obj M).obj
        (Diagonal.sourceStalkModule f x) ≅
      (Koszul.coefficientComplex M (Diagonal.equations f x)).homology n :=
  Diagonal.torIsoHomology f x M n

/-- The finite bound is the proved local coordinate-list length, for arbitrary coefficients. -/
theorem arbitraryCoefficientBound (M : ModuleCat (Diagonal.ambientStalk f x)) (n : ℕ)
    (hn : (Diagonal.equations f x).length < n) :
    IsZero (((Tor (ModuleCat (Diagonal.ambientStalk f x)) n).obj M).obj
      (Diagonal.sourceStalkModule f x)) :=
  Diagonal.isZero_tor_above_length f x M n hn

end Motivic.MotivicTest.SmoothDiagonalKoszul
