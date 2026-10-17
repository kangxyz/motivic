/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.GenericTor

/-!
# Consumers of actual generic closed-intersection Tor

These consumers use the literal Cartesian square, the actual two stalks, and
the actual generic point. Finite coefficient generation and Artinian support
are conclusions; neither is supplied as an assumed target record.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.Intersection Motivic.LengthEuler RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.GenericIntersectionTor

variable {W D T P : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j) (w : W)

/-- The actual full intersection local ring, with no reduction or residue-field replacement. -/
noncomputable def actualSumQuotient :
    (ambientStalk i (a w)) ⧸
      (RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom) ≃+*
      W.presheaf.stalk w :=
  stalkQuotientSumEquiv a b i j sq w

variable [IsLocallyNoetherian W] (hw : w ∈ genericPoints W)

include hw in
/-- Artinianness is proved for the actual sum quotient, not for the ambient stalk. -/
theorem actualArtinianSupport :
    IsArtinianRing ((ambientStalk i (a w)) ⧸
      (RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom)) :=
  stalk_sum_quotient_isArtinian a b i j sq w hw

variable [IsNoetherianRing (ambientStalk i (a w))]
  (hregular : ∃ s : List (ambientStalk i (a w)),
    IsRegular (ambientStalk i (a w)) s ∧ RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)

include hw hregular in
/-- Every actual Tor correction has finite length over the ambient local ring. -/
theorem actualTorLength (n : ℕ) :
    Module.length (ambientStalk i (a w))
      (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w))) ≠ ⊤ :=
  (finiteLengthSupport_tor_of_regular_kernel a b i j sq w hw hregular).finite_length n

/-- The integer coefficient is constructed from the actual finite categorical Tor lengths. -/
noncomputable def actualCoefficient : ℤ :=
  torEulerCoefficient a b i j sq w hw hregular

variable (s : List (ambientStalk i (a w)))
  (hker : RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)
  (hs : IsRegular (ambientStalk i (a w)) s)

include hs in
/-- Any actual regular list computes the same coefficient through genuine Koszul homology. -/
theorem actualEulerComparison :
    actualCoefficient a b i j sq w hw hregular =
      chainEuler
        (Koszul.coefficientComplex
          (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s)
        (Intersection.finiteHomology a b i j sq w hw s hker) :=
  torEulerCoefficient_eq_chainEuler a b i j sq w hw s hker hs hregular

end Motivic.MotivicTest.GenericIntersectionTor
