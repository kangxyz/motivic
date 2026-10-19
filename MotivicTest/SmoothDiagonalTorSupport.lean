/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.SmoothTorSupport

/-!
# Actual diagonal Tor support and module-length consumers

The annihilator consumer has arbitrary coefficients. Actual module-length
finiteness keeps finite generation, Noetherianity, and minimality at the
literal diagonal-kernel-plus-annihilator support explicit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.SmoothDiagonalTorSupport
open _root_.AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X)
  (M : ModuleCat (Diagonal.ambientStalk f x))

/-- The literal support ideal annihilates actual diagonal Tor with arbitrary coefficients. -/
theorem actualSupport (n : ℕ) :
    RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (Diagonal.ambientStalk f x) M ≤
      Module.annihilator (Diagonal.ambientStalk f x)
        (((Tor (ModuleCat (Diagonal.ambientStalk f x)) n).obj M).obj
          (Diagonal.sourceStalkModule f x)) :=
  Diagonal.support_le_annihilator_tor f x M n

/-- The explicit local support criterion gives finite module length in every actual Tor degree. -/
theorem finiteLengthAtMinimalSupport [IsNoetherianRing (Diagonal.ambientStalk f x)]
    [Module.Finite (Diagonal.ambientStalk f x) M]
    (hm : IsLocalRing.maximalIdeal (Diagonal.ambientStalk f x) ∈
      (RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (Diagonal.ambientStalk f x) M).minimalPrimes) (n : ℕ) :
    Module.length (Diagonal.ambientStalk f x)
      (((Tor (ModuleCat (Diagonal.ambientStalk f x)) n).obj M).obj
        (Diagonal.sourceStalkModule f x)) ≠ ⊤ :=
  (Diagonal.finiteLengthSupport_tor_of_mem_minimalPrimes_support f x M hm).finite_length n

/-- Artinian support constructs finite module lengths and finite degree support together. -/
theorem artinianSupport [IsNoetherianRing (Diagonal.ambientStalk f x)]
    [Module.Finite (Diagonal.ambientStalk f x) M]
    [IsArtinianRing ((Diagonal.ambientStalk f x) ⧸
      (RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (Diagonal.ambientStalk f x) M))] :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat (Diagonal.ambientStalk f x)) n).obj M).obj
        (Diagonal.sourceStalkModule f x)) :=
  Diagonal.finiteLengthSupport_tor_of_artinian_support f x M

end Motivic.MotivicTest.SmoothDiagonalTorSupport
