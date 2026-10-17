/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.WholeFiberRemainingList
public import Motivic.AlgebraicGeometry.Cycles.IntegralGenericFiniteImage
public import Motivic.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Motivic.Algebra.Homology.KoszulDimensionZeroHead

/-!
# Generic lifts and the absent-component remaining Euler term

The actual Cartesian remaining-incidence square gives a lift precisely on
the inverse image of the full exterior support. Existence uses the proved
scheme-pullback point-lifting theorem; it does not identify an arbitrary
scheme fiber product with a set-theoretic fiber product. A closed immersion
reflects genericity, so a lift over an actual image-incidence generic is a
genuine generic of the original component incidence.

When no such lift exists, the literal exterior immersion ideal has unit
stalk at the same image-side point. Its actual quotient module and its Koszul
complex for the identical original remaining list are zero. Finite homology
has empty support, so the genuine chain Euler characteristic is zero without
regularity, a kernel-generating hypothesis, or a Noetherian hypothesis.

Finally, the original smooth incidence component generator supplies the
required image-ideal equality from the actual finite-image factorization.
No reducedness of an exterior, global cycle equality, or associativity is
asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ExteriorImageComponentGeometry

open LengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (C : IntegralClosedSubscheme (F.incidenceMap G).image)
  (P : FiniteCorrespondenceGenerator f h)
  (hC : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)

/-- A compatible actual exterior point lifts through the proved Cartesian
square, retaining both original point projections. -/
theorem remainingToImage_fiber_lift (y : F.leftImageIncidence G H)
    (e : exterior F G H C)
    (he : exteriorInclusion F G H C e = F.leftImageIncidenceInclusion G H y) :
    ∃ w : P.incidence H, remainingToImage F G H C P hC w = y ∧
      remainingToExterior F G H C P hC w = e :=
  Scheme.exists_preimage_of_isPullback
    (remainingToImage_isPullback F G H C P hC) y e he.symm

/-- The actual component-incidence range is exactly the inverse image of
the full exterior closed-immersion range. -/
theorem remainingToImage_range :
    Set.range (remainingToImage F G H C P hC) =
      (F.leftImageIncidenceInclusion G H) ⁻¹' Set.range (exteriorInclusion F G H C) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨remainingToExterior F G H C P hC w,
      congrArg (fun m => m w) (remainingToImage_square F G H C P hC).symm⟩
  · rintro ⟨e, he⟩
    obtain ⟨w, hw, -⟩ := remainingToImage_fiber_lift F G H C P hC y e he
    exact ⟨w, hw⟩

/-- Above an actual image-incidence generic, the lift is genuinely generic
in the original component incidence and retains the chosen exterior point. -/
theorem remainingToImage_fiber_lift_generic (y : genericPoints (F.leftImageIncidence G H))
    (e : exterior F G H C)
    (he : exteriorInclusion F G H C e = F.leftImageIncidenceInclusion G H y.1) :
    ∃ w : genericPoints (P.incidence H), remainingToImage F G H C P hC w.1 = y.1 ∧
      remainingToExterior F G H C P hC w.1 = e := by
  obtain ⟨w, hw, he⟩ := remainingToImage_fiber_lift F G H C P hC y.1 e he
  have hwgen : w ∈ genericPoints (P.incidence H) :=
    mem_genericPoints_of_image_generic (remainingToImage F G H C P hC) w (hw.symm ▸ y.2)
  exact ⟨⟨w, hwgen⟩, hw, he⟩

/-- The genuine generic-lift condition is precisely actual exterior-range
membership at the identical image-side point. -/
theorem remainingToImage_exists_generic_iff (y : genericPoints (F.leftImageIncidence G H)) :
    (∃ w : genericPoints (P.incidence H), remainingToImage F G H C P hC w.1 = y.1) ↔
      F.leftImageIncidenceInclusion G H y.1 ∈ Set.range (exteriorInclusion F G H C) := by
  constructor
  · rintro ⟨w, hw⟩
    have hy : y.1 ∈ Set.range (remainingToImage F G H C P hC) := ⟨w.1, hw⟩
    rw [remainingToImage_range F G H C P hC] at hy
    exact hy
  · rintro ⟨e, he⟩
    obtain ⟨w, hw, -⟩ := remainingToImage_fiber_lift_generic F G H C P hC y e he
    exact ⟨w, hw⟩

variable (y : genericPoints (F.leftImageIncidence G H))
  (hno : ¬ ∃ w : genericPoints (P.incidence H), remainingToImage F G H C P hC w.1 = y.1)

include hno

/-- Absence of a genuine generic lift forces the literal exterior ideal
stalk to be the unit ideal at the same original image-side point. -/
theorem remainingExterior_ker_stalk_eq_top_of_no_genericLift :
    (exteriorInclusion F G H C).ker.stalk (F.leftImageIncidenceInclusion G H y.1) = ⊤ := by
  apply closedImmersion_ker_stalk_eq_top
  exact fun hy => hno ((remainingToImage_exists_generic_iff F G H C P hC y).mpr hy)

/-- The actual quotient ring, with its original image-product stalk scalars,
is zero in the absent-lift case. -/
theorem remainingExterior_quotient_subsingleton_of_no_genericLift :
    Subsingleton
      (((F.leftIntermediateImageProduct G H).presheaf.stalk
        (F.leftImageIncidenceInclusion G H y.1)) ⧸
        (exteriorInclusion F G H C).ker.stalk (F.leftImageIncidenceInclusion G H y.1)) :=
  Ideal.Quotient.subsingleton_iff.mpr
    (remainingExterior_ker_stalk_eq_top_of_no_genericLift F G H C P hC y hno)

/-- The literal quotient is a zero object in the original stalk's module
category; no replacement scalar action is chosen. -/
theorem remainingExterior_quotient_isZero_of_no_genericLift :
    IsZero (ModuleCat.of
      ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (F.leftImageIncidenceInclusion G H y.1))
      (((F.leftIntermediateImageProduct G H).presheaf.stalk
        (F.leftImageIncidenceInclusion G H y.1)) ⧸
        (exteriorInclusion F G H C).ker.stalk (F.leftImageIncidenceInclusion G H y.1))) := by
  have := remainingExterior_quotient_subsingleton_of_no_genericLift F G H C P hC y hno
  exact ModuleCat.isZero_of_subsingleton _

variable (s : List ((pullback h h).presheaf.stalk
  (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y.1))))

/-- The identical original remaining list has actual finite homology on the
zero quotient: every homology object is zero, so its length support is empty. -/
theorem remainingQuotient_finiteHomology_of_no_genericLift :
    FiniteHomology (Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (F.leftImageIncidenceInclusion G H y.1))
        (((F.leftIntermediateImageProduct G H).presheaf.stalk
          (F.leftImageIncidenceInclusion G H y.1)) ⧸
          (exteriorInclusion F G H C).ker.stalk (F.leftImageIncidenceInclusion G H y.1)))
      (F.leftTargetRemainingList G H (F.leftImageIncidenceInclusion G H y.1) s)) := by
  have hzero := Functor.map_isZero
    (Koszul.coefficientFunctor
      (F.leftTargetRemainingList G H (F.leftImageIncidenceInclusion G H y.1) s))
    (remainingExterior_quotient_isZero_of_no_genericLift F G H C P hC y hno)
  exact FiniteLengthSupport.of_isZero_outside _ ∅ (by simp)
    (fun n _ => Functor.map_isZero (HomologicalComplex.homologyFunctor _ _ n) hzero)

/-- The absent-lift term has zero genuine quotient-chain Euler for the same
actual middle list, with finite homology proved from the zero module. -/
theorem remainingQuotient_chainEuler_zero_of_no_genericLift :
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (F.leftImageIncidenceInclusion G H y.1))
        (((F.leftIntermediateImageProduct G H).presheaf.stalk
          (F.leftImageIncidenceInclusion G H y.1)) ⧸
          (exteriorInclusion F G H C).ker.stalk (F.leftImageIncidenceInclusion G H y.1)))
      (F.leftTargetRemainingList G H (F.leftImageIncidenceInclusion G H y.1) s))
      (remainingQuotient_finiteHomology_of_no_genericLift F G H C P hC y hno s) = 0 := by
  have := remainingExterior_quotient_subsingleton_of_no_genericLift F G H C P hC y hno
  exact Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ _

end Motivic.ExteriorImageComponentGeometry

namespace Motivic.ExteriorImageComponentGeometry

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (z : genericPoints (F.incidence G))

/-- The original smooth component generator supplies the exact image-ideal
equality used above, via the actual finite image inside the whole pair image. -/
theorem smoothComponent_imageKernel :
    ((IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
      (F.incidenceMap G).imageι).ker = (F.smoothIncidenceComponentGenerator k G z).val := by
  let := F.incidenceToImage_isFinite G
  have himage :
      (IntegralClosedSubscheme.pointClosure z.1).finiteImage (F.incidenceMap G).toImage =
        IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1) := by
    apply Subtype.ext
    exact IntegralClosedSubscheme.pointClosure_image_kernel (F.incidenceMap G).toImage z.1
  rw [F.smoothIncidenceComponentGenerator_val k G z]
  change ((IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)).finiteImage
      (F.incidenceMap G).imageι).val =
    ((IntegralClosedSubscheme.pointClosure z.1).finiteImage (F.incidenceMap G)).val
  rw [← himage, ← IntegralClosedSubscheme.finiteImage_comp]
  simp only [IntegralClosedSubscheme.finiteImage, Scheme.Hom.toImage_imageι]

end Motivic.ExteriorImageComponentGeometry
