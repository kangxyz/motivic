/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.StalkModules

/-!
# Consumers of the actual closed-intersection stalk modules

The coefficient module is the actual second stalk with the actual transported
closed-immersion action. The tests derive finite generation and the exact
annihilator, and compare actual Tor without assuming regular coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.IntersectionStalkModules

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)

/-- This module has the second stalk as its actual underlying type. -/
theorem actualCoefficientType :
    (Intersection.coefficientStalkModule i d j t hp : Type u) = T.presheaf.stalk t := rfl

/-- Its annihilator is the actual transported closed-stalk kernel. -/
theorem actualAnnihilator :
    Module.annihilator (Intersection.ambientStalk i d)
        (Intersection.coefficientStalkModule i d j t hp) =
      RingHom.ker (Intersection.coefficientStalkMap i d j t hp).hom :=
  Intersection.coefficientStalkModule_annihilator i d j t hp

/-- Closed-stalk surjectivity constructs the coefficient finiteness instance. -/
theorem actualCoefficientFinite [IsClosedImmersion j] :
    Module.Finite (Intersection.ambientStalk i d)
      (Intersection.coefficientStalkModule i d j t hp) := inferInstance

variable [IsClosedImmersion i] (s : List (Intersection.ambientStalk i d))
  (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s)
  (hs : IsRegular (Intersection.ambientStalk i d) s)

/-- A real categorical Tor degree is computed by the existing finite Koszul resolution. -/
noncomputable def actualTorComparison (n : ℕ) :
    ((Tor (ModuleCat (Intersection.ambientStalk i d)) n).obj
      (Intersection.coefficientStalkModule i d j t hp)).obj
        (Intersection.sourceStalkModule i d) ≅
      (Koszul.coefficientComplex (Intersection.coefficientStalkModule i d j t hp) s).homology n :=
  Intersection.torIsoHomology i d j t hp s hker hs n

include hker hs in
/-- Higher corrections are only discarded above the proved full regular-list bound. -/
theorem actualHigherTorBound (n : ℕ) (hn : s.length < n) :
    IsZero (((Tor (ModuleCat (Intersection.ambientStalk i d)) n).obj
      (Intersection.coefficientStalkModule i d j t hp)).obj
        (Intersection.sourceStalkModule i d)) :=
  Intersection.isZero_tor_above_length i d j t hp s hker hs n hn

end Motivic.MotivicTest.IntersectionStalkModules
