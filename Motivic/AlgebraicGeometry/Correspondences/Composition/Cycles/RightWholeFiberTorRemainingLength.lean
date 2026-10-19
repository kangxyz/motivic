/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.SemilocalLengthDescent
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.RightWholeFiberTorRemainingList
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.RightWholeFiberTorRemainingFiber

/-!
# Actual whole right remaining-Y finite homology

The accepted right whole-coefficient common-list comparison retains the
original maximal-localization and source-stalk scalar actions. Its homology
lengths and the public generic finite-maximal-spectrum Koszul criterion give
a conditional whole-coefficient adapter. The accepted geometric full-fiber
support theorem then discharges every original source length at a genuine
right final image-incidence generic point. No whole finite homology is assumed.

Numerical projection and total-complex Euler comparison are separate steps.
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
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- The actual finite image-product section map supplies the coefficient action. -/
local instance rightRemainingLengthCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original supported-Tor remaining Koszul complex at one full-fiber point,
with the one common middle list transported by its actual stalk equality. -/
abbrev rightFirstStageSourceRemainingKoszul
    (s : List ((CategoryTheory.Limits.pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :=
  _root_.ChainComplex.Koszul.coefficientComplex (F.rightFirstStageSupportedStalkTor G H x.1 n)
    ((F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
      ((F.rightSupportMiddlePair G H).stalkMap x.1).hom)

variable (q : MaximalSpectrum
  (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p))

/-- Actual localized coefficient homology uses the canonical localization ring. -/
local instance rightRemainingLengthLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- The localization algebra map uses the same canonical semiring structure. -/
local instance rightRemainingLengthLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

/-- Flat maximal localization, the constructed common-list chain map and the
actual source structure-stalk equivalence identify every genuine homology length. -/
theorem rightFirstStageWholeRemainingLocalizedHomology_length
    (s : List ((CategoryTheory.Limits.pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)))) (n r : ℕ) :
    Module.length (Localization.AtPrime q.asIdeal)
      ((ModuleCat.extendScalars (S := Localization.AtPrime q.asIdeal) (algebraMap
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
        (Localization.AtPrime q.asIdeal))).obj
          ((F.rightFirstStageWholeRemainingKoszul G H V p s n).homology r)) =
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk
      (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1)
      ((F.rightFirstStageSourceRemainingKoszul G H V p s
        (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q) n).homology r) := by
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p
  let C := F.rightFirstStageWholeRemainingKoszul G H V p s n
  let D := F.rightFirstStageSourceRemainingKoszul G H V p s
    (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q) n
  let e := originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 p q
  let φ := e.hom.hom
  exact (finiteAlgebraLocalizedHomologyIso T C q r).symm.toLinearEquiv.length_eq.trans
    (((HomologicalComplex.homologyFunctor _ _ r).mapIso
      (F.rightFirstStageWholeRemainingLocalizedIso G H V p q s n)).toLinearEquiv.length_eq.trans
      (((D.sc r).mapHomologyIso (ModuleCat.restrictScalars φ)).toLinearEquiv.length_eq.trans
        (_root_.ModuleCat.length_restrictScalars_of_surjective φ
          e.commRingCatIsoToRingEquiv.surjective _)))

/-- The generic finite-maximal-spectrum Koszul criterion descends the proved
lengths on every original source branch to the actual whole coefficient. -/
theorem rightFirstStageWholeRemaining_finiteHomology_of_source
    (s : List ((CategoryTheory.Limits.pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)
    (hsource : ∀ x : {w : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H w = V.2.fromSpec p},
      FiniteHomology (F.rightFirstStageSourceRemainingKoszul G H V p s x n)) :
    FiniteHomology (F.rightFirstStageWholeRemainingKoszul G H V p s n) := by
  have := coordinateFinite (F.rightIntermediateImageMap G H) V.2
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p
  have : Finite (MaximalSpectrum T) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal) T
  apply _root_.ChainComplex.Koszul.coefficient_finiteHomology_of_maximalLengths T
    (F.rightFirstStageWholeLocalizedCoefficient G H V p n)
    (F.rightFirstStageWholeRemainingList G H V p s)
  intro q r
  rw [(finiteAlgebraLocalizedHomologyIso T
    (F.rightFirstStageWholeRemainingKoszul G H V p s n) q r).toLinearEquiv.length_eq]
  rw [F.rightFirstStageWholeRemainingLocalizedHomology_length G H V p q s n r]
  exact (hsource (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q)).finite_length r

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  (y : F.rightImageIncidence G H)
  (hy : y ∈ genericPoints (F.rightImageIncidence G H))
  (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)

include hy hp in
/-- Genuine generic-point support proves finite homology of the actual whole
localized remaining Koszul complex, in every first-stage Tor degree. -/
theorem rightFirstStageWholeRemaining_finiteHomology
    (s : List ((pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hs : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    FiniteHomology (F.rightFirstStageWholeRemainingKoszul G H V p s n) := by
  have hyV : F.rightImageIncidenceInclusion G H y ∈ V.1 := by
    rw [← hp]
    exact V.2.range_fromSpec.subset (Set.mem_range_self p)
  let P : F.rightIntermediateImageProduct G H → Prop := fun z =>
    ∀ (t : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z))),
      (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H z) = Ideal.ofList t →
      ∀ (x : {w : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H w = z}) (m : ℕ),
        FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex
            (F.rightFirstStageSupportedStalkTor G H x.1 m)
          ((F.rightFiberMiddleList G H z t x).map
            ((F.rightSupportMiddlePair G H).stalkMap x.1).hom))
  have hP : P (F.rightImageIncidenceInclusion G H y) := by
    intro t ht x m
    exact F.rightSupportedTorRemainingFiber_finiteHomology G H V y hy hyV t ht x m
  have hQ : P (V.2.fromSpec p) := (congrArg P hp).mpr hP
  exact F.rightFirstStageWholeRemaining_finiteHomology_of_source G H V p s n
    (fun x => hQ s hs x n)

include hy hp in
/-- Smoothness constructs the one original diagonal list and proves actual whole
remaining finite homology simultaneously in every first-stage Tor degree. -/
theorem exists_rightFirstStageWholeRemaining_finiteHomology [Smooth g] :
    ∃ s : List ((pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
      (pullback.diagonal g).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s ∧
      ∀ n, FiniteHomology (F.rightFirstStageWholeRemainingKoszul G H V p s n) := by
  have hr : F.rightImageMiddlePair G H (V.2.fromSpec p) ∈
      Set.range (pullback.diagonal g) := by
    rw [hp]
    exact F.rightImageIncidence_middle_mem_diagonal G H y
  obtain ⟨s, hs, hker⟩ := F.exists_rightTargetRemainingList G H (V.2.fromSpec p) hr
  exact ⟨s, hs, hker,
    F.rightFirstStageWholeRemaining_finiteHomology G H V p y hy hp s hker⟩

include hy in
/-- For every original final image generic point, an actual affine chart and one
smooth middle list give whole remaining finite homology; no coordinate lift is assumed. -/
theorem exists_rightFirstStageWholeRemaining_chart [Smooth g] :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V)),
      V.2.fromSpec p = F.rightImageIncidenceInclusion G H y ∧
      ∃ s : List ((pullback g g).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))),
        RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
          (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
        (pullback.diagonal g).ker.stalk
          (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s ∧
        ∀ n, FiniteHomology (F.rightFirstStageWholeRemainingKoszul G H V p s n) := by
  obtain ⟨U, hU, p, hp⟩ :=
    FiniteAffineChart.exists_targetChart (F.rightImageIncidenceInclusion G H y)
  exact ⟨⟨U, hU⟩, p, hp,
    F.exists_rightFirstStageWholeRemaining_finiteHomology G H ⟨U, hU⟩ p y hy hp⟩

end Motivic.FiniteCorrespondenceGenerator
