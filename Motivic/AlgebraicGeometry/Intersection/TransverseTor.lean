/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.GenericTor
public import Motivic.Algebra.Homology.TorZeroQuotients

/-!
# Actual transverse closed-intersection Tor multiplicity

For a Cartesian square of closed immersions, zeroth categorical Tor is the
full intersection stalk, with its actual ambient scalar action. A regular
list generating the literal first stalk kernel kills positive Tor when the
same list is additionally weakly regular on the actual second stalk.
This extra coefficient regularity is explicit; it is not asserted for every
closed support. At a generic point, the resulting Tor Euler coefficient is
the ordinary full generic stalk length, including any nilpotents.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open RingTheory.Sequence Motivic.LengthEuler

universe u

namespace Motivic.Intersection

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D)

set_option backward.isDefEq.respectTransparency false in
/-- Quotienting by the literal closed-stalk kernel gives the actual source module. -/
def sourceKernelQuotientIso [IsClosedImmersion i] :
    ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸
      RingHom.ker (i.stalkMap d).hom) ≅ sourceStalkModule i d := by
  let := (i.stalkMap d).hom.toAlgebra
  let μ : ambientStalk i d →ₐ[ambientStalk i d] D.presheaf.stalk d := Algebra.ofId _ _
  exact (Ideal.quotientKerAlgEquivOfSurjective
    (show Function.Surjective μ from i.stalkMap_surjective d)).toLinearEquiv.toModuleIso

variable (j : T ⟶ P) (t : T) (hp : i d = j t)

set_option backward.isDefEq.respectTransparency false in
/-- The transported literal coefficient kernel presents the actual coefficient module. -/
def coefficientKernelQuotientIso [IsClosedImmersion j] :
    ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸
      RingHom.ker (coefficientStalkMap i d j t hp).hom) ≅
      coefficientStalkModule i d j t hp := by
  let := (coefficientStalkMap i d j t hp).hom.toAlgebra
  let μ : ambientStalk i d →ₐ[ambientStalk i d] T.presheaf.stalk t := Algebra.ofId _ _
  have hμ : Function.Surjective μ := coefficientStalkMap_surjective i d j t hp
  exact (Ideal.quotientKerAlgEquivOfSurjective hμ).toLinearEquiv.toModuleIso

section Cartesian

variable {W : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j) (w : W)

set_option backward.isDefEq.respectTransparency false in
/-- The quotient by the sum of literal kernels is the full intersection stalk as a module. -/
def sumKernelQuotientStalkIso :
    ModuleCat.of (ambientStalk i (a w)) ((ambientStalk i (a w)) ⧸
      (RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom)) ≅
      sourceStalkModule (a ≫ i) w := by
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip inferInstance
  exact (Ideal.quotientEquivAlgOfEq (ambientStalk i (a w))
    (stalkMap_kernel_eq_sup a b i j sq w).symm).toLinearEquiv.toModuleIso ≪≫
      sourceKernelQuotientIso (a ≫ i) w

/-- The tensor product of the actual source stalks is the actual full intersection stalk. -/
def tensorStalkIso :
    coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w) ⊗
        sourceStalkModule i (a w) ≅ sourceStalkModule (a ≫ i) w :=
  tensorIso (coefficientKernelQuotientIso i (a w) j (b w) (point_eq a b i j sq w)).symm
      (sourceKernelQuotientIso i (a w)).symm ≪≫
    (tensorQuotientSupEquiv
      (RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom)
      (RingHom.ker (i.stalkMap (a w)).hom)).toModuleIso ≪≫
    (Ideal.quotientEquivAlgOfEq (ambientStalk i (a w)) (sup_comm _ _)).toLinearEquiv.toModuleIso ≪≫
    sumKernelQuotientStalkIso i j a b sq w

/-- Zeroth categorical Tor is the actual full intersection stalk, without transversality. -/
def torZeroIsoStalk :
    ((Tor (ModuleCat (ambientStalk i (a w))) 0).obj
      (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
        (sourceStalkModule i (a w)) ≅ sourceStalkModule (a ≫ i) w :=
  torZeroIsoTensor _ _ ≪≫ tensorStalkIso i j a b sq w

set_option backward.isDefEq.respectTransparency false in
/-- Zeroth Tor length is the actual intersection-ring length by surjective stalk restriction. -/
theorem length_tor_zero_eq_stalk :
    Module.length (ambientStalk i (a w))
      (((Tor (ModuleCat (ambientStalk i (a w))) 0).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w))) =
      Module.length (W.presheaf.stalk w) (W.presheaf.stalk w) := by
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip inferInstance
  exact (torZeroIsoStalk i j a b sq w).toLinearEquiv.length_eq.trans
    (length_stalk_restrictScalars (a ≫ i) w)

end Cartesian

variable [IsClosedImmersion i] (s : List (ambientStalk i d))
  (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s)
  (hs : IsRegular (ambientStalk i d) s)
  (hT : IsWeaklyRegular (coefficientStalkModule i d j t hp) s)

include hker hs hT in
/-- Actual positive Tor vanishes under additional regularity on the actual coefficient stalk. -/
theorem isZero_tor_succ_of_coefficient_regular (n : ℕ) :
    IsZero (((Tor (ModuleCat (ambientStalk i d)) (n + 1)).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) :=
  (Koszul.isZero_finiteTor_succ_of_weaklyRegular
    (coefficientStalkModule i d j t hp) s hs.toIsWeaklyRegular hT n).of_iso
      (((Tor (ModuleCat (ambientStalk i d)) (n + 1)).obj
        (coefficientStalkModule i d j t hp)).mapIso (quotientStalkIso i d s hker).symm)

end Motivic.Intersection

namespace Motivic.Intersection

variable {W D T P : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j)
  [IsLocallyNoetherian W] (w : W) (hw : w ∈ genericPoints W)
  [IsNoetherianRing (ambientStalk i (a w))]
  (hregular : ∃ s : List (ambientStalk i (a w)),
    IsRegular (ambientStalk i (a w)) s ∧ RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)
  (s : List (ambientStalk i (a w)))
  (hker : RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)
  (hs : IsRegular (ambientStalk i (a w)) s)
  (hT : IsWeaklyRegular
    (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s)

include hker hs hT in
/-- Genuine coefficient transversality turns the full Tor Euler sum into full stalk length. -/
theorem torEulerCoefficient_eq_stalk_length_of_coefficient_regular :
    torEulerCoefficient a b i j sq w hw hregular =
      ((Module.length (W.presheaf.stalk w) (W.presheaf.stalk w)).toNat : ℤ) := by
  unfold torEulerCoefficient
  rw [signedLengthSum_eq_sum _ _ _ {0}]
  · simp only [Finset.sum_singleton, pow_zero, one_mul, integerLength]
    rw [length_tor_zero_eq_stalk i j a b sq w]
  · intro n hn
    by_contra hn0
    have hn0 : n ≠ 0 := by simpa using hn0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton
        (((Tor (ModuleCat (ambientStalk i (a w))) (m + 1)).obj
          (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
            (sourceStalkModule i (a w))) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_tor_succ_of_coefficient_regular i (a w) j (b w)
          (point_eq a b i j sq w) s hker hs hT m)
    exact hn Module.length_eq_zero

include hker hs hT in
/-- The transverse generic coefficient is the ordinary full generic multiplicity. -/
theorem torEulerCoefficient_eq_genericMultiplicity_of_coefficient_regular :
    torEulerCoefficient a b i j sq w hw hregular =
      (genericMultiplicity ⟨w, hw⟩ : ℤ) :=
  torEulerCoefficient_eq_stalk_length_of_coefficient_regular
    a b i j sq w hw hregular s hker hs hT

end Motivic.Intersection
