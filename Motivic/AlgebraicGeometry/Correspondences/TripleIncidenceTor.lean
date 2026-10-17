/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleCombinedRegularity
public import Motivic.AlgebraicGeometry.Intersection.ExteriorKoszulTorSupport
public import Motivic.AlgebraicGeometry.Intersection.GenericTor

/-!
# Canonical total Tor coefficients of actual triple incidence

The source is the actual combined two-diagonal fourfold product and the
coefficient is the original exterior product of the three correspondence
supports, both in the original six-factor ambient. Their categorical Tor is
canonical and independent of any chosen regular list. The proved joint
regular kernel and actual generic intersection support establish finite
length in every degree and a finite degree bound. No parenthesization
comparison, coefficient-flatness hypothesis or assumed finite support is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual ambient stalk of full triple incidence in the six-factor product. -/
abbrev tripleIncidenceAmbientStalk (w : F.tripleIncidence G H) :=
  Intersection.ambientStalk
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w)

/-- The original exterior support stalk, with the literal transported ambient scalars. -/
abbrev tripleIncidenceSupportStalkModule (w : F.tripleIncidence G H) :
    ModuleCat (F.tripleIncidenceAmbientStalk G H w) :=
  Intersection.coefficientStalkModule
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w) (F.tripleSupportProductInclusion G H)
    ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w)
    (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w)

/-- The full fourfold-product stalk with scalars through the genuine two-diagonal inclusion. -/
abbrev tripleIncidenceFourfoldStalkModule (w : F.tripleIncidence G H) :
    ModuleCat (F.tripleIncidenceAmbientStalk G H w) :=
  Intersection.sourceStalkModule
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w)

/-- Categorical Tor of the original exterior support and actual combined-diagonal stalks. -/
def tripleIncidenceTor (w : F.tripleIncidence G H) (n : ℕ) :
    ModuleCat (F.tripleIncidenceAmbientStalk G H w) :=
  ((Tor (ModuleCat (F.tripleIncidenceAmbientStalk G H w)) n).obj
    (F.tripleIncidenceSupportStalkModule G H w)).obj
      (F.tripleIncidenceFourfoldStalkModule G H w)

/-- The original exterior-support stalk is finite over the genuine six-factor ambient. -/
instance tripleIncidenceSupportStalkModule_finite (w : F.tripleIncidence G H) :
    Module.Finite (F.tripleIncidenceAmbientStalk G H w)
      (F.tripleIncidenceSupportStalkModule G H w) :=
  inferInstanceAs (Module.Finite _ (Intersection.coefficientStalkModule _ _ _ _ _))

variable [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
  [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]

/-- The joint regular kernel and full generic incidence support prove finite
lengths and finite degree support for canonical total Tor. -/
theorem tripleIncidenceTor_finiteLengthSupport (w : F.tripleIncidence G H)
    (hw : w ∈ genericPoints (F.tripleIncidence G H)) :
    FiniteLengthSupport (F.tripleIncidenceTor G H w) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact Intersection.finiteLengthSupport_tor_of_regular_kernel
    (F.tripleIncidenceFourfoldInclusion G H)
    (F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H)
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.tripleIncidence_sixfold_isPullback G H) w hw
    (exists_regular_kernel_correspondenceFourfoldDiagonal f g h i
      (F.tripleIncidenceFourfoldInclusion G H w))

/-- The canonical full triple-incidence coefficient retains every higher Tor correction. -/
def tripleIncidenceTorCoefficient (w : genericPoints (F.tripleIncidence G H)) : ℤ :=
  signedLengthSum (F.tripleIncidenceTor G H w.val) (fun n => (-1 : ℤ) ^ n)
    (F.tripleIncidenceTor_finiteLengthSupport G H w.val w.property)

/-- Every actual total Tor degree at a generic triple point has finite ambient length. -/
theorem tripleIncidenceTor_length_ne_top (w : genericPoints (F.tripleIncidence G H)) (n : ℕ) :
    Module.length (F.tripleIncidenceAmbientStalk G H w.val)
      (F.tripleIncidenceTor G H w.val n) ≠ ⊤ :=
  (F.tripleIncidenceTor_finiteLengthSupport G H w.val w.property).finite_length n

omit [Flat f] [Flat i] in
/-- Generic full incidence support gives finite homology for every list of
actual combined-kernel generators, even before regularity is used. -/
theorem tripleIncidenceKoszul_finiteHomology
    (w : genericPoints (F.tripleIncidence G H))
    (r : List (F.tripleIncidenceAmbientStalk G H w.val))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList r) :
    FiniteHomology
      (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w.val) r) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact Intersection.finiteHomology _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H)
    w.val w.property r hker

/-- Any genuine regular presentation of the combined kernel computes the same
canonical total coefficient. The presentation does not define the coefficient. -/
theorem tripleIncidenceTorCoefficient_eq_chainEuler
    (w : genericPoints (F.tripleIncidence G H))
    (r : List (F.tripleIncidenceAmbientStalk G H w.val))
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w.val) r)
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList r) :
    F.tripleIncidenceTorCoefficient G H w =
      chainEuler (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w.val) r)
        (F.tripleIncidenceKoszul_finiteHomology G H w r hker) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact Intersection.torEuler_eq_chainEuler _ _ _ _
    (F.tripleIncidence_sixfold_isPullback G H) w.val w.property r hker hr

end Motivic.FiniteCorrespondenceGenerator
