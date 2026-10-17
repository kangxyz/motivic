/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.TransverseTor

/-!
# Consumers of genuine transverse closed-intersection Tor

The zero-degree consumer needs only the actual closed Cartesian square.
The positive-degree and multiplicity consumers additionally retain the same
literal kernel-generating list and its weak regularity on the actual second
stalk. The final consumer deduces positivity from the resulting ordinary
generic length, under precisely those transversality hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.Intersection RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.TransverseTor

variable {W D T P : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j) (w : W)

/-- The actual zeroth Tor object is the full source stalk, including nilpotents. -/
def actualTorZero :
    ((Tor (ModuleCat (ambientStalk i (a w))) 0).obj
      (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
        (sourceStalkModule i (a w)) ≅ sourceStalkModule (a ≫ i) w :=
  torZeroIsoStalk i j a b sq w

/-- Length changes from the actual ambient local ring to the actual intersection ring. -/
theorem actualTorZeroLength :
    Module.length (ambientStalk i (a w))
      (((Tor (ModuleCat (ambientStalk i (a w))) 0).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w))) =
      Module.length (W.presheaf.stalk w) (W.presheaf.stalk w) :=
  length_tor_zero_eq_stalk i j a b sq w

variable (s : List (ambientStalk i (a w)))
  (hker : RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)
  (hs : IsRegular (ambientStalk i (a w)) s)
  (hT : IsWeaklyRegular
    (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s)

include hker hs hT in
omit [IsClosedImmersion j] in
/-- Every positive categorical Tor degree vanishes, not merely degrees above a bound. -/
theorem actualPositiveTorZero (n : ℕ) (hn : 0 < n) :
    IsZero (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
      (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
        (sourceStalkModule i (a w))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact isZero_tor_succ_of_coefficient_regular i (a w) j (b w)
    (point_eq a b i j sq w) s hker hs hT m

variable [IsLocallyNoetherian W] (hw : w ∈ genericPoints W)
  [IsNoetherianRing (ambientStalk i (a w))]

include hT in
/-- The coefficient built from the supplied genuine regular list is ordinary generic length. -/
theorem actualTransverseCoefficient :
    torEulerCoefficient a b i j sq w hw ⟨s, hs, hker⟩ =
      (genericMultiplicity ⟨w, hw⟩ : ℤ) :=
  torEulerCoefficient_eq_genericMultiplicity_of_coefficient_regular
    a b i j sq w hw ⟨s, hs, hker⟩ s hker hs hT

include hT in
/-- A transverse coefficient is positive, by the full generic-stalk length theorem. -/
theorem actualTransverseCoefficient_pos :
    0 < torEulerCoefficient a b i j sq w hw ⟨s, hs, hker⟩ := by
  rw [actualTransverseCoefficient a b i j sq w s hker hs hT hw]
  exact_mod_cast genericMultiplicity_pos (⟨w, hw⟩ : genericPoints W)

end Motivic.MotivicTest.TransverseTor
