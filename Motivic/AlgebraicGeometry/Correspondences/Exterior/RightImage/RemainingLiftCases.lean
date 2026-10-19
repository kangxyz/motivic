/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.RightImage.ComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.RemainingLiftCases

/-!
# Generic lifts and the absent right-component remaining Euler term

The actual Cartesian remaining Y-incidence square gives a lift precisely on
its full right exterior support. The proved closed immersion reflects
image-side genericity; no generic lift is assumed to exist.

With no generic lift, the literal exterior immersion ideal has unit stalk
at the same image-side point. Its actual quotient, with its original stalk
scalars, is zero. The identical original remaining Y list therefore has
finite homology with empty support and genuine chain Euler zero, without
regularity or a kernel-generating hypothesis.

The full exterior retains its possible nilpotents. Field and SmoothSite
parameters come only from the shared right exterior API; no perfectness,
connectedness, reducedness or flatness of F over Y is assumed. The accepted
two-correspondence smooth-component image-kernel theorem is imported for
actual component consumers. No Tor, global cycle, or bracket equality is
asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.RightExteriorImageComponentGeometry
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

open _root_.HomologicalComplex.ModuleLengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)
  (P : FiniteCorrespondenceGenerator Y.hom W.hom)
  (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)

/-- A compatible actual exterior point lifts through the proved Cartesian
square, retaining both original point projections. -/
theorem remainingToImage_fiber_lift (y : F.rightImageIncidence G H)
    (e : F.rightImageComponentExterior G H C)
    (he : F.rightImageComponentExteriorInclusion G H C e = F.rightImageIncidenceInclusion G H y) :
    ∃ w : F.incidence P, remainingToImage F G H C P hC w = y ∧
      remainingToExterior F G H C P hC w = e :=
  Scheme.exists_preimage_of_isPullback
    (remainingToImage_isPullback F G H C P hC) y e he.symm

/-- The actual component-incidence range is exactly the inverse image of
the full exterior closed-immersion range. -/
theorem remainingToImage_range :
    Set.range (remainingToImage F G H C P hC) =
      (F.rightImageIncidenceInclusion G H) ⁻¹'
        Set.range (F.rightImageComponentExteriorInclusion G H C) := by
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
theorem remainingToImage_fiber_lift_generic (y : genericPoints (F.rightImageIncidence G H))
    (e : F.rightImageComponentExterior G H C)
    (he : F.rightImageComponentExteriorInclusion G H C e = F.rightImageIncidenceInclusion G H y.1) :
    ∃ w : genericPoints (F.incidence P), remainingToImage F G H C P hC w.1 = y.1 ∧
      remainingToExterior F G H C P hC w.1 = e := by
  obtain ⟨w, hw, he⟩ := remainingToImage_fiber_lift F G H C P hC y.1 e he
  have hwgen : w ∈ genericPoints (F.incidence P) :=
    mem_genericPoints_of_image_generic (remainingToImage F G H C P hC) w (hw.symm ▸ y.2)
  exact ⟨⟨w, hwgen⟩, hw, he⟩

/-- The genuine generic-lift condition is precisely actual exterior-range
membership at the identical image-side point. -/
theorem remainingToImage_exists_generic_iff (y : genericPoints (F.rightImageIncidence G H)) :
    (∃ w : genericPoints (F.incidence P), remainingToImage F G H C P hC w.1 = y.1) ↔
      F.rightImageIncidenceInclusion G H y.1 ∈
        Set.range (F.rightImageComponentExteriorInclusion G H C) := by
  constructor
  · rintro ⟨w, hw⟩
    have hy : y.1 ∈ Set.range (remainingToImage F G H C P hC) := ⟨w.1, hw⟩
    rw [remainingToImage_range F G H C P hC] at hy
    exact hy
  · rintro ⟨e, he⟩
    obtain ⟨w, hw, -⟩ := remainingToImage_fiber_lift_generic F G H C P hC y e he
    exact ⟨w, hw⟩

variable (y : genericPoints (F.rightImageIncidence G H))
  (hno : ¬ ∃ w : genericPoints (F.incidence P), remainingToImage F G H C P hC w.1 = y.1)

include hno

/-- Absence of a genuine generic lift excludes the actual exterior support
at the original image-side point. -/
theorem remainingExterior_not_mem_range_of_no_genericLift :
    F.rightImageIncidenceInclusion G H y.1 ∉
      Set.range (F.rightImageComponentExteriorInclusion G H C) :=
  fun hy => hno ((remainingToImage_exists_generic_iff F G H C P hC y).mpr hy)

/-- Absence of a genuine generic lift forces the literal exterior ideal
stalk to be the unit ideal at the same original image-side point. -/
theorem remainingExterior_ker_stalk_eq_top_of_no_genericLift :
    (F.rightImageComponentExteriorInclusion G H C).ker.stalk
        (F.rightImageIncidenceInclusion G H y.1) = ⊤ := by
  apply closedImmersion_ker_stalk_eq_top
  exact remainingExterior_not_mem_range_of_no_genericLift F G H C P hC y hno

/-- The actual quotient ring, with its original image-product stalk scalars,
is zero in the absent-lift case. -/
theorem remainingExterior_quotient_subsingleton_of_no_genericLift :
    Subsingleton
      (((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1)) ⧸
        (F.rightImageComponentExteriorInclusion G H C).ker.stalk
          (F.rightImageIncidenceInclusion G H y.1)) :=
  Ideal.Quotient.subsingleton_iff.mpr
    (remainingExterior_ker_stalk_eq_top_of_no_genericLift F G H C P hC y hno)

/-- The literal quotient is a zero object in the original stalk's module
category; no replacement scalar action is chosen. -/
theorem remainingExterior_quotient_isZero_of_no_genericLift :
    IsZero (ModuleCat.of
      ((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1))
      (((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1)) ⧸
        (F.rightImageComponentExteriorInclusion G H C).ker.stalk
          (F.rightImageIncidenceInclusion G H y.1))) := by
  have := remainingExterior_quotient_subsingleton_of_no_genericLift F G H C P hC y hno
  exact ModuleCat.isZero_of_subsingleton _

variable (s : List ((pullback Y.hom Y.hom).presheaf.stalk
  (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y.1))))

/-- The identical original remaining list has actual finite homology on the
zero quotient: every homology object is zero, so its length support is empty. -/
theorem remainingQuotient_finiteHomology_of_no_genericLift :
    FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageIncidenceInclusion G H y.1)) ⧸
          (F.rightImageComponentExteriorInclusion G H C).ker.stalk
          (F.rightImageIncidenceInclusion G H y.1)))
      (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y.1) s)) := by
  have hzero := Functor.map_isZero
    (_root_.ChainComplex.Koszul.coefficientFunctor
      (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y.1) s))
    (remainingExterior_quotient_isZero_of_no_genericLift F G H C P hC y hno)
  exact FiniteLengthSupport.of_isZero_outside _ ∅ (by simp)
    (fun n _ => Functor.map_isZero (HomologicalComplex.homologyFunctor _ _ n) hzero)

/-- The absent-lift term has zero genuine quotient-chain Euler for the same
actual middle list, with finite homology proved from the zero module. -/
theorem remainingQuotient_chainEuler_zero_of_no_genericLift :
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageIncidenceInclusion G H y.1))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageIncidenceInclusion G H y.1)) ⧸
          (F.rightImageComponentExteriorInclusion G H C).ker.stalk
          (F.rightImageIncidenceInclusion G H y.1)))
      (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y.1) s))
      (remainingQuotient_finiteHomology_of_no_genericLift F G H C P hC y hno s) = 0 := by
  have := remainingExterior_quotient_subsingleton_of_no_genericLift F G H C P hC y hno
  exact _root_.ChainComplex.Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ _

end Motivic.RightExteriorImageComponentGeometry
