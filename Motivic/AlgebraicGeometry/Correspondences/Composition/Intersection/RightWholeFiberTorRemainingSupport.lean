/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.RightRemainingSupport
public import Motivic.Aglib.AlgebraicGeometry.Intersection.WholeFiberTorStalk
public import Motivic.Aglib.Algebra.Homology.Koszul.ScalarRestriction.Length

/-!
# Right remaining-Y-diagonal finite lengths for the actual whole-fiber Tor coefficient

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
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [(correspondenceSixfoldAmbient f g h i).IsSeparated]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (U : (F.rightIntermediateImageProduct G H).affineOpens)

/-- The original structure-stalk module of the actual constructed whole-fiber
Tor equalizer, retaining its genuine first-stage quotient action. -/
abbrev rightWholeFiberTorOriginalStalk (x : F.rightIntermediateSupportProduct G H) (n : ℕ) :
    ModuleCat.{u} ((F.rightIntermediateSupportProduct G H).presheaf.stalk x) :=
  (Stalk.functor x).obj
    (closedIntersectionTorGlued (F.tripleSupportProductInclusion G H)
      (correspondenceSecondAmbientInclusion f g h i)
      (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
      (F.rightIntermediate_ambient_isPullback G H)
      (wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
        (correspondenceSecondAmbientInclusion f g h i)
        (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
        (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) U) n)

omit [IsSeparated g] in
/-- Actual locally Noetherian geometry and the original Tor-stalk attachment
prove finite generation at every point of the entire source inverse image. -/
theorem rightWholeFiberTorOriginalStalk_finite
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : F.rightIntermediateSupportProduct G H)
    (hx : x ∈ (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :
    Module.Finite ((F.rightIntermediateSupportProduct G H).presheaf.stalk x)
      (F.rightWholeFiberTorOriginalStalk G H U x n) :=
  wholeFiberTorGluedStalk_finite (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) U x hx n

variable (w : F.tripleIncidence G H)
  (s : List ((pullback g g).presheaf.stalk
    (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))))
  (hker : (pullback.diagonal g).ker.stalk
      (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w)) =
    Ideal.ofList s)

include hker in
/-- The actual remaining-incidence stalk kernel annihilates the remaining
Koszul homology of the constructed whole-fiber Tor coefficient in every degree. -/
theorem rightWholeFiberTorRemaining_kernel_annihilator (n m : ℕ) :
    RingHom.ker ((F.tripleIncidenceToRightSupportProduct G H).stalkMap w).hom ≤
      Module.annihilator _
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (F.rightWholeFiberTorOriginalStalk G H U
            (F.tripleIncidenceToRightSupportProduct G H w) n)
          (s.map ((F.rightSupportMiddlePair G H).stalkMap
            (F.tripleIncidenceToRightSupportProduct G H w)).hom)).homology m) :=
  F.rightRemainingKoszul_kernel_annihilator G H w s hker _ m

include hker in
/-- At every actual generic final-incidence point in the whole source open,
the constructed first-stage Tor coefficient has finite remaining Koszul homology.
The input includes only original geometry and literal middle equations. -/
theorem rightWholeFiberTorRemaining_finiteHomology
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (hw : w ∈ genericPoints (F.tripleIncidence G H))
    (hU : F.tripleIncidenceToRightSupportProduct G H w ∈
      (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex
        (F.rightWholeFiberTorOriginalStalk G H U
          (F.tripleIncidenceToRightSupportProduct G H w) n)
        (s.map ((F.rightSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToRightSupportProduct G H w)).hom)) := by
  have hclosed : IsClosedImmersion (F.rightIntermediateAmbientInclusion G H) := inferInstance
  have hfinite := (IsClosedImmersion.iff_isFinite_and_mono
    (F.rightIntermediateAmbientInclusion G H)).mp hclosed
  have : LocallyOfFiniteType (F.rightIntermediateAmbientInclusion G H) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfinite.1).2
  have := LocallyOfFiniteType.isLocallyNoetherian (F.rightIntermediateAmbientInclusion G H)
  have := F.rightWholeFiberTorOriginalStalk_finite G H U
    (F.tripleIncidenceToRightSupportProduct G H w) hU n
  exact F.rightRemainingKoszul_finiteHomology G H w s hker hw _

include hker in
/-- The same finite lengths hold over the genuine local ring of the whole
inverse image, using the literal open-inclusion map on the remaining list. -/
theorem rightWholeFiberTorCoefficientRemaining_finiteHomology
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (hw : w ∈ genericPoints (F.tripleIncidence G H))
    (hU : F.tripleIncidenceToRightSupportProduct G H w ∈
      (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :
    let x : ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme :=
      ⟨F.tripleIncidenceToRightSupportProduct G H w, hU⟩
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex
        ((Stalk.functor x).obj
          (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
            (correspondenceSecondAmbientInclusion f g h i)
            (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
            (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) U n))
        ((s.map ((F.rightSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToRightSupportProduct G H w)).hom).map
            (((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap x).hom)) := by
  dsimp only
  let x : ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme :=
    ⟨F.tripleIncidenceToRightSupportProduct G H w, hU⟩
  let e := Stalk.openRestrictionOriginalIso
    ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).ι x
    (closedIntersectionTorGlued (F.tripleSupportProductInclusion G H)
      (correspondenceSecondAmbientInclusion f g h i)
      (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
      (F.rightIntermediate_ambient_isPullback G H)
      (wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
        (correspondenceSecondAmbientInclusion f g h i)
        (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
        (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) U) n)
  apply (_root_.ChainComplex.Koszul.coefficientRestrict_finiteLengthSupport_iff
    (((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap x).hom
    (((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap_surjective x) _ _).mp
  exact (F.rightWholeFiberTorRemaining_finiteHomology G H U w s hker hw hU n).of_iso
    (fun m => (HomologicalComplex.homologyFunctor _ _ m).mapIso
      (_root_.ChainComplex.Koszul.coefficientIso e.symm _))

end Motivic.FiniteCorrespondenceGenerator
