/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.RemainingSupport
public import Motivic.Aglib.AlgebraicGeometry.Intersection.WholeFiberTorStalk
public import Motivic.Aglib.Algebra.Homology.Koszul.ScalarRestriction.Length

/-!
# Remaining-diagonal finite lengths for the actual whole-fiber Tor coefficient

The coefficient here is the stalk of the constructed finite-cover Tor equalizer
on the actual first-stage support. Its finite generation comes from the proved
attachment to genuine supported Tor. The remaining diagonal kernel is proved
from the original pullback geometry and annihilates its Koszul homology. At an
actual generic triple-incidence point this proves finite length in every
degree. The result also retains the original open-restriction stalk action on
the coefficient over the whole finite inverse image.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [IsSeparated g] [IsSeparated h]
  [(correspondenceSixfoldAmbient f g h i).IsSeparated]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (U : (F.leftIntermediateImageProduct G H).affineOpens)

/-- The original structure-stalk module of the actual constructed whole-fiber
Tor equalizer, retaining its genuine first-stage quotient action. -/
abbrev leftWholeFiberTorOriginalStalk (x : F.leftIntermediateSupportProduct G H) (n : ℕ) :
    ModuleCat.{u} ((F.leftIntermediateSupportProduct G H).presheaf.stalk x) :=
  (Stalk.functor x).obj
    (closedIntersectionTorGlued (F.tripleSupportProductInclusion G H)
      (correspondenceFirstDiagonalInclusion f g h i)
      (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
      (F.leftIntermediate_ambient_isPullback G H)
      (wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
        (correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U) n)

/-- Actual locally Noetherian geometry and the original Tor-stalk attachment
prove finite generation at every point of the entire source inverse image. -/
theorem leftWholeFiberTorOriginalStalk_finite
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : F.leftIntermediateSupportProduct G H)
    (hx : x ∈ (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :
    Module.Finite ((F.leftIntermediateSupportProduct G H).presheaf.stalk x)
      (F.leftWholeFiberTorOriginalStalk G H U x n) :=
  wholeFiberTorGluedStalk_finite (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U x hx n

variable (w : F.tripleIncidence G H)
  (s : List ((pullback h h).presheaf.stalk
    (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))))
  (hker : (pullback.diagonal h).ker.stalk
      (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w)) =
    Ideal.ofList s)

include hker in
/-- The actual remaining-incidence stalk kernel annihilates the remaining
Koszul homology of the constructed whole-fiber Tor coefficient in every degree. -/
theorem leftWholeFiberTorRemaining_kernel_annihilator (n m : ℕ) :
    RingHom.ker ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap w).hom ≤
      Module.annihilator _
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (F.leftWholeFiberTorOriginalStalk G H U
            (F.tripleIncidenceToLeftSupportProduct G H w) n)
          (s.map ((F.leftSupportMiddlePair G H).stalkMap
            (F.tripleIncidenceToLeftSupportProduct G H w)).hom)).homology m) :=
  F.remainingKoszul_kernel_annihilator G H w s hker _ m

include hker in
/-- At every actual generic final-incidence point in the whole source open,
the constructed first-stage Tor coefficient has finite remaining Koszul homology.
The input includes only original geometry and literal middle equations. -/
theorem leftWholeFiberTorRemaining_finiteHomology
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (hw : w ∈ genericPoints (F.tripleIncidence G H))
    (hU : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex
        (F.leftWholeFiberTorOriginalStalk G H U
          (F.tripleIncidenceToLeftSupportProduct G H w) n)
        (s.map ((F.leftSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToLeftSupportProduct G H w)).hom)) := by
  have hclosed : IsClosedImmersion (F.leftIntermediateAmbientInclusion G H) := inferInstance
  have hfinite := (IsClosedImmersion.iff_isFinite_and_mono
    (F.leftIntermediateAmbientInclusion G H)).mp hclosed
  have : LocallyOfFiniteType (F.leftIntermediateAmbientInclusion G H) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfinite.1).2
  have := LocallyOfFiniteType.isLocallyNoetherian (F.leftIntermediateAmbientInclusion G H)
  have := F.leftWholeFiberTorOriginalStalk_finite G H U
    (F.tripleIncidenceToLeftSupportProduct G H w) hU n
  exact F.remainingKoszul_finiteHomology G H w s hker hw _

include hker in
/-- The same finite lengths hold over the genuine local ring of the whole
inverse image, using the literal open-inclusion map on the remaining list. -/
theorem leftWholeFiberTorCoefficientRemaining_finiteHomology
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (hw : w ∈ genericPoints (F.tripleIncidence G H))
    (hU : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :
    let x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme :=
      ⟨F.tripleIncidenceToLeftSupportProduct G H w, hU⟩
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex
        ((Stalk.functor x).obj
          (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
            (correspondenceFirstDiagonalInclusion f g h i)
            (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
            (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U n))
        ((s.map ((F.leftSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToLeftSupportProduct G H w)).hom).map
            (((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap x).hom)) := by
  dsimp only
  let x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme :=
    ⟨F.tripleIncidenceToLeftSupportProduct G H w, hU⟩
  let e := Stalk.openRestrictionOriginalIso
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).ι x
    (closedIntersectionTorGlued (F.tripleSupportProductInclusion G H)
      (correspondenceFirstDiagonalInclusion f g h i)
      (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
      (F.leftIntermediate_ambient_isPullback G H)
      (wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
        (correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U) n)
  apply (_root_.ChainComplex.Koszul.coefficientRestrict_finiteLengthSupport_iff
    (((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap x).hom
    (((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap_surjective x) _ _).mp
  exact (F.leftWholeFiberTorRemaining_finiteHomology G H U w s hker hw hU n).of_iso
    (fun m => (HomologicalComplex.homologyFunctor _ _ m).mapIso
      (_root_.ChainComplex.Koszul.coefficientIso e.symm _))

end Motivic.FiniteCorrespondenceGenerator
