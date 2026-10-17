/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.StalkModules
public import Motivic.AlgebraicGeometry.IdealSheaf.StalkKernel
public import Motivic.AlgebraicGeometry.Correspondences.IntersectionAmbientIdeal
public import Motivic.AlgebraicGeometry.Cycles.GenericStalkSupport

/-!
# Finite categorical Tor at genuine generic closed-intersection points

For an actual Cartesian square of closed immersions, the kernel of its
ambient stalk map is the sum of the two literal closed-stalk kernels. At a
generic point of a locally Noetherian intersection, its quotient is therefore
Artinian. The second actual stalk is a finite ambient module and its
annihilator is its literal kernel, as proved in `StalkModules`.

A regular list for the first literal kernel now gives finite-length support
of the actual categorical Tor of the two actual source stalks. The resulting
canonical integer coefficient is the alternating sum of all Tor lengths.
No coefficient regularity, higher-Tor vanishing, reduced structure, or
finite-support target record is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence Motivic.LengthEuler

universe u

namespace Motivic.Intersection

variable {W D T P : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
  (sq : IsPullback a b i j)

include sq in
/-- The two images of an actual intersection point are the same ambient point. -/
theorem point_eq (w : W) : i (a w) = j (b w) :=
  congrArg (fun f : W ⟶ P => f w) sq.w

variable [IsClosedImmersion i] [IsClosedImmersion j]

/-- The literal kernel of the ambient intersection stalk is the sum of both source kernels. -/
theorem stalkMap_kernel_eq_sup (w : W) :
    RingHom.ker ((a ≫ i).stalkMap w).hom =
      RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom := by
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip inferInstance
  have hc :
      RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom =
        j.ker.stalk (i (a w)) := by
    rw [coefficientStalkMap, CommRingCat.hom_comp, ← RingHom.comap_ker,
      ← j.ker_stalk (b w), j.ker.stalk_congr_comap (point_eq a b i j sq w)]
  rw [← (a ≫ i).ker_stalk w, ker_comp_eq_sup_of_isPullback a b i j sq,
    Scheme.IdealSheafData.stalk_sup, hc]
  exact congrArg (fun I => I ⊔ j.ker.stalk (i (a w))) (i.ker_stalk (a w))

/-- The sum quotient is the actual full intersection stalk, including its nilpotents. -/
def stalkQuotientSumEquiv (w : W) :
    (ambientStalk i (a w)) ⧸
      (RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom) ≃+*
      W.presheaf.stalk w := by
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip inferInstance
  rw [← stalkMap_kernel_eq_sup a b i j sq w]
  exact stalkQuotientKerEquiv (a ≫ i) w

variable [IsLocallyNoetherian W] (w : W) (hw : w ∈ genericPoints W)

include hw in
/-- The sum of both literal source-stalk kernels cuts out the actual Artinian generic stalk. -/
theorem stalk_sum_quotient_isArtinian :
    IsArtinianRing ((ambientStalk i (a w)) ⧸
      (RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom)) := by
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip inferInstance
  rw [← stalkMap_kernel_eq_sup a b i j sq w]
  exact stalk_quotient_ker_isArtinian (a ≫ i) w hw

variable [IsNoetherianRing (ambientStalk i (a w))]
  (s : List (ambientStalk i (a w)))
  (hker : RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)

include hw hker in
/-- Genuine generic intersection support proves finite length and finite degree support
for coefficient Koszul homology, without regularity of the coefficient stalk. -/
theorem finiteHomology :
    FiniteHomology
      (Koszul.coefficientComplex
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s) := by
  have : IsArtinianRing ((ambientStalk i (a w)) ⧸
      (Ideal.ofList s ⊔ Module.annihilator (ambientStalk i (a w))
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)))) := by
    rw [coefficientStalkModule_annihilator, ← hker]
    exact stalk_sum_quotient_isArtinian a b i j sq w hw
  exact Koszul.finiteHomology_of_artinian_support_quotient _ s

variable (hs : IsRegular (ambientStalk i (a w)) s)

include hw hker hs in
/-- At a genuine generic intersection point the categorical Tor of both actual stalks
has finite module lengths and finite degree support. -/
theorem finiteLengthSupport_tor :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w))) :=
  (finiteHomology a b i j sq w hw s hker).of_iso
    (fun n => (torIsoHomology i (a w) j (b w) (point_eq a b i j sq w) s hker hs n).symm)

/-- The actual Tor Euler sum agrees with the full coefficient Koszul Euler length. -/
theorem torEuler_eq_chainEuler :
    signedLengthSum (fun n =>
      ((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w)))
      (fun n => (-1 : ℤ) ^ n) (finiteLengthSupport_tor a b i j sq w hw s hker hs) =
      chainEuler
        (Koszul.coefficientComplex
          (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s)
        (finiteHomology a b i j sq w hw s hker) :=
  signedLengthSum_eq_of_iso _ _ _
    (fun n => torIsoHomology i (a w) j (b w) (point_eq a b i j sq w) s hker hs n)

variable (hregular : ∃ s : List (ambientStalk i (a w)),
  IsRegular (ambientStalk i (a w)) s ∧ RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)

include hw hregular in
/-- Existence of actual regular generators suffices, without an input finite-support record. -/
theorem finiteLengthSupport_tor_of_regular_kernel :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w))) := by
  obtain ⟨s, hs, hker⟩ := hregular
  exact finiteLengthSupport_tor a b i j sq w hw s hker hs

/-- The canonical generic-intersection coefficient retains all higher Tor corrections. -/
def torEulerCoefficient : ℤ :=
  signedLengthSum (fun n =>
    ((Tor (ModuleCat (ambientStalk i (a w))) n).obj
      (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
        (sourceStalkModule i (a w)))
    (fun n => (-1 : ℤ) ^ n)
    (finiteLengthSupport_tor_of_regular_kernel a b i j sq w hw hregular)

include hs in
/-- Any genuine regular list computes the same canonical coefficient. -/
theorem torEulerCoefficient_eq_chainEuler :
    torEulerCoefficient a b i j sq w hw hregular =
      chainEuler
        (Koszul.coefficientComplex
          (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s)
        (finiteHomology a b i j sq w hw s hker) :=
  torEuler_eq_chainEuler a b i j sq w hw s hker hs

include hker hs in
/-- Every finite list of actual regular generators gives an explicit finite formula,
including every possible higher-Tor correction through its full length. -/
theorem torEulerCoefficient_eq_sum :
    torEulerCoefficient a b i j sq w hw hregular =
      ∑ n ∈ Finset.range (s.length + 1), (-1 : ℤ) ^ n *
        integerLength
          (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
            (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
              (sourceStalkModule i (a w)))
          ((finiteLengthSupport_tor_of_regular_kernel
            a b i j sq w hw hregular).finite_length n) := by
  apply signedLengthSum_eq_sum
  intro n hn
  by_contra hnot
  have hn' : s.length < n := by simpa using hnot
  have : Subsingleton
      (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
          (sourceStalkModule i (a w))) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_tor_above_length i (a w) j (b w) (point_eq a b i j sq w) s hker hs n hn')
  exact hn Module.length_eq_zero

end Motivic.Intersection
