/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.WholeFiber.RightRemainingList
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorBounded
public import Motivic.Aglib.Algebra.Homology.Koszul.ExteriorCoefficientComparison

/-!
# Actual right whole Tor coefficients with the common remaining-Y list

The constructed whole inverse-image coefficient, its original scalar stalks,
and its actual localized section module receive the single target-middle list.
Their genuine Tor comparisons identify the resulting remaining Koszul complexes
with the original geometric supported Tor coefficients. Maximal localization
uses the whole finite algebra and its proved equivalence with the complete
original source fiber. No coefficient module or source-list comparison is
assumed, and no finite-length conclusion is claimed here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The separatedness instance used in this module. -/
local instance intersectionRightWholeFiberTorRemainingListSeparated
    : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The existing supported geometric first-stage Tor with its original support-stalk action. -/
abbrev rightFirstStageSupportedStalkTor (w : F.rightIntermediateSupportProduct G H) (n : ℕ) :=
  closedIntersectionSupportedStalkTor (correspondenceSecondAmbientInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H) w n

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- The original coordinate homomorphism supplies all whole-algebra scalar actions. -/
local instance rightTorRemainingCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual whole-preimage coefficient stalk restricted through its literal
open inclusion, retaining the original first-stage support local ring. -/
abbrev rightFirstStageWholeOriginalStalkModule
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :=
  (ModuleCat.restrictScalars
    (((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap
      ⟨x.1, wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V p x⟩).hom).obj
    ((Stalk.functor (X := ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).toScheme)
      ⟨x.1, wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V p x⟩).obj
      (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
        (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
        (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
        (F.rightIntermediateImageMap G H) V n))

/-- The actual constructed coefficient at every source-fiber point recovers
original supported Tor, without assuming a pointwise comparison. -/
def rightFirstStageWholeOriginalStalkIso
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :
    F.rightFirstStageWholeOriginalStalkModule G H V p x n ≅
      F.rightFirstStageSupportedStalkTor G H x.1 n :=
  wholeFiberTorCoefficientOriginalStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) V
    ⟨x.1, wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V p x⟩ n

/-- On the actual whole coefficient, the common target list gives precisely
the original remaining Koszul complex at every original source-fiber point. -/
def rightFirstStageWholeRemainingStalkIso
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :
    _root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageWholeOriginalStalkModule G H V p
        x n)
        ((F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
          (originalFiberStalkMap (F.rightIntermediateImageMap G H) V.2 p x).hom) ≅
      _root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageSupportedStalkTor G H x.1 n)
        ((F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
          ((F.rightSupportMiddlePair G H).stalkMap x.1).hom) :=
  (_root_.ChainComplex.Koszul.coefficientFunctor _).mapIso (F.rightFirstStageWholeOriginalStalkIso G
      H V p x n) ≪≫
    eqToIso (congrArg (_root_.ChainComplex.Koszul.coefficientComplex
        (F.rightFirstStageSupportedStalkTor G H x.1 n))
      (F.rightOriginalFiberRemainingList_map G H V p s x))

/-- The same actual whole-coefficient comparison keeps the original six-factor
remaining equations and their literal ambient-to-support stalk map. -/
def rightFirstStageWholeRemainingAmbientListIso
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :
    _root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageWholeOriginalStalkModule G H V p
        x n)
        ((F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
          (originalFiberStalkMap (F.rightIntermediateImageMap G H) V.2 p x).hom) ≅
      _root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageSupportedStalkTor G H x.1 n)
        (((F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
          (F.rightAmbientMiddleStalkMap G H x.1).hom).map
            ((F.rightIntermediateAmbientInclusion G H).stalkMap x.1).hom) :=
  F.rightFirstStageWholeRemainingStalkIso G H V p s x n ≪≫
    eqToIso (congrArg (_root_.ChainComplex.Koszul.coefficientComplex
        (F.rightFirstStageSupportedStalkTor G H x.1 n))
      (F.rightAmbientMiddleList_map G H x.1
        (F.rightFiberMiddleList G H (V.2.fromSpec p) s x)).symm)

/-- The actual original-scalar remaining homology comparison holds in every
outer Tor degree and every remaining Koszul degree on the entire source fiber. -/
def rightFirstStageWholeRemainingHomologyIso
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (n r : ℕ) :
    (_root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageWholeOriginalStalkModule G H V
        p x n)
        ((F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
          (originalFiberStalkMap (F.rightIntermediateImageMap G H) V.2 p x).hom)).homology r ≅
      (_root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageSupportedStalkTor G H x.1 n)
        ((F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
          ((F.rightSupportMiddlePair G H).stalkMap x.1).hom)).homology r :=
  (HomologicalComplex.homologyFunctor _ _ r).mapIso
    (F.rightFirstStageWholeRemainingStalkIso G H V p s x n)

/-- The single target-middle list is transported to the entire localized finite
algebra before any maximal point or original source branch is selected. -/
def rightFirstStageWholeRemainingList
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p)))) :
    List (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p) :=
  ((F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
    (targetStalkLocalizationIso V.2 p).hom.hom).map
      (algebraMap (Localization.AtPrime p.asIdeal) _)

/-- The genuine remaining Koszul complex on the actual whole-section Tor module. -/
abbrev rightFirstStageWholeRemainingKoszul
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (n : ℕ) :=
  _root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageWholeLocalizedCoefficient G H V p
      n)
    (F.rightFirstStageWholeRemainingList G H V p s)

variable (q : MaximalSpectrum
  (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p))

/-- Categorical localizations use their canonical commutative-ring structure. -/
local instance rightTorRemainingLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- Scalar maps and categorical modules use the same canonical localization semiring. -/
local instance rightTorRemainingLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

/-- The actual maximal localization of the constructed whole-section module
is the genuine supported Tor at the corresponding original source point. -/
def rightFirstStageWholeMaximalCoefficientIso (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
        Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
      (Localization.AtPrime q.asIdeal))).obj
        (F.rightFirstStageWholeLocalizedCoefficient G H V p n) ≅
    (ModuleCat.restrictScalars
      (originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q).hom.hom).obj
      (F.rightFirstStageSupportedStalkTor G H
        (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1 n) := by
  have : ((Scheme.Modules.restrictFunctor ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
      (F.rightFirstStageWholeAmbientCoefficient G H V n)).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  let e₁ := (ModuleCat.extendScalars (S := Localization.AtPrime q.asIdeal) (algebraMap
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
        Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
      (Localization.AtPrime q.asIdeal))).mapIso
      (wholeFiberTorLocalizedSectionsIso (F.tripleSupportProductInclusion G H)
        (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
        (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
        (F.rightIntermediateImageMap G H) V p n).symm
  let e₂ := RelativeFiniteEuler.originalWholeModuleSourceIso
      (F.rightIntermediateImageMap G H) V.2 p (F.rightFirstStageWholeAmbientCoefficient G H V n) q
  let e₃ := (ModuleCat.restrictScalars
      (originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q).hom.hom).mapIso
      (wholeFiberTorGluedStalkIso (F.tripleSupportProductInclusion G H)
        (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
        (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
        (F.rightIntermediateImageMap G H) V _
        (wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V p
          (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q)) n)
  exact e₁ ≪≫ e₂ ≪≫ e₃

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] in
/-- The actual whole-algebra list becomes the original common middle image list
under each literal maximal-localization-to-source-stalk homomorphism. -/
theorem rightFirstStageWholeRemainingList_source
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p)))) :
    ((F.rightFirstStageWholeRemainingList G H V p s).map
      (algebraMap
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
        (Localization.AtPrime q.asIdeal))).map
        (originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q).hom.hom =
      (F.rightFiberMiddleList G H (V.2.fromSpec p) s
        (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q)).map
          ((F.rightSupportMiddlePair G H).stalkMap
            (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1).hom := by
  let R := Localization.AtPrime p.asIdeal
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p
  let Q := Localization.AtPrime q.asIdeal
  let t := (F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
    (targetStalkLocalizationIso V.2 p).hom.hom
  have hm : (t.map (algebraMap R T)).map (algebraMap T Q) = t.map (algebraMap R Q) := by
    rw [List.map_map, ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq R T Q]
  change ((t.map (algebraMap R T)).map (algebraMap T Q)).map
    (originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q).hom.hom = _
  rw [hm]
  exact (originalSourceLocalizationIso_list (F.rightIntermediateImageMap G H) V.2 p q
    (F.rightTargetRemainingList G H (V.2.fromSpec p) s)).trans
      (F.rightOriginalFiberRemainingList_map G H V p s
        (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q))

/-- Localization of the actual whole remaining Koszul complex recovers the
original supported Tor Koszul complex, with its literal original scalar action. -/
def rightFirstStageWholeRemainingLocalizedIso
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (n : ℕ) :
    ((ModuleCat.extendScalars (algebraMap
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
        Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
      (Localization.AtPrime q.asIdeal))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (F.rightFirstStageWholeRemainingKoszul G H V p s n) ≅
    (Functor.mapHomologicalComplex (ModuleCat.restrictScalars
      (originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q).hom.hom)
        (ComplexShape.down ℕ)).obj
      (_root_.ChainComplex.Koszul.coefficientComplex
        (F.rightFirstStageSupportedStalkTor G H
          (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1 n)
        ((F.rightFiberMiddleList G H (V.2.fromSpec p) s
          (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q)).map
            ((F.rightSupportMiddlePair G H).stalkMap
              (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1).hom)) :=
  _root_.ChainComplex.Koszul.coefficientExtendIso _ _ _ ≪≫
    (_root_.ChainComplex.Koszul.coefficientFunctor _).mapIso
      (F.rightFirstStageWholeMaximalCoefficientIso G H V p q n) ≪≫
    _root_.ChainComplex.Koszul.coefficientRestrictIso _ _ _ ≪≫
    (Functor.mapHomologicalComplex (ModuleCat.restrictScalars
      (originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q).hom.hom)
        (ComplexShape.down ℕ)).mapIso
      (eqToIso (congrArg (_root_.ChainComplex.Koszul.coefficientComplex
        (F.rightFirstStageSupportedStalkTor G H
          (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1 n))
        (F.rightFirstStageWholeRemainingList_source G H V p q s)))

end Motivic.FiniteCorrespondenceGenerator
