/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorRemainingList
public import Mathlib.Data.DFinsupp.WellFounded

/-!
# Finite length of the original whole remaining-Koszul homology

Actual maximal localization and the original finite-map stalk comparisons
allow finite length to descend from every original source point in the whole
fiber. The genuine local finite-length or support argument is an explicit,
separate input; finite generation alone is never used to infer finite length.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler

open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
open _root_.HomologicalComplex.ModuleLengthEuler

/-- Categorical and tensor localization use the canonical commutative ring structure. -/
local instance lengthDescentLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- The same canonical semiring is used in all tensor localization comparisons. -/
local instance lengthDescentLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

private def maximalSubmoduleEmbedding (S : Type u) [CommRing S] (M : ModuleCat.{u} S) :
    Submodule S M ↪o ∀ q : MaximalSpectrum S,
      Submodule (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⊗[S] M) := by
  let g := fun (N : Submodule S M) (q : MaximalSpectrum S) =>
    N.localized' (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
      (TensorProduct.mk S (Localization.AtPrime q.asIdeal) M 1)
  refine OrderEmbedding.ofMapLEIff g ?_
  intro N N'
  constructor
  · intro h
    apply Submodule.le_of_localization_maximal
      (fun P _ => Localization.AtPrime P ⊗[S] M)
      (fun P _ => TensorProduct.mk S (Localization.AtPrime P) M 1)
    intro P hP
    exact h ⟨P, hP⟩
  · intro h q
    exact (Submodule.localized'gi (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
      (TensorProduct.mk S (Localization.AtPrime q.asIdeal) M 1)).gc.monotone_l h

private theorem length_ne_top_of_maximal (S : Type u) [CommRing S]
    [Finite (MaximalSpectrum S)] (M : ModuleCat.{u} S)
    (hM : ∀ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M) ≠ ⊤) :
    Module.length S M ≠ ⊤ := by
  have hfin (q : MaximalSpectrum S) : IsFiniteLength (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[S] M) := by
    apply Module.length_ne_top_iff.mp
    rw [← (finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime q.asIdeal) M).length_eq]
    exact hM q
  let Q := fun q : MaximalSpectrum S =>
    Submodule (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⊗[S] M)
  have : ∀ q : MaximalSpectrum S, WellFoundedLT (Q q) := fun q =>
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfin q)).2
  have : ∀ q : MaximalSpectrum S, WellFoundedGT (Q q) := fun q =>
    _root_.isNoetherian_iff.mp (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfin q)).1
  let e := maximalSubmoduleEmbedding S M
  have : IsArtinian S M := e.wellFoundedLT
  let ed : (Submodule S M)ᵒᵈ ↪o ∀ q, (Q q)ᵒᵈ :=
    OrderEmbedding.ofMapLEIff (fun N q => e N q) (fun _ _ => e.le_iff_le)
  have : _root_.IsNoetherian S M := _root_.isNoetherian_iff.mpr ed.wellFoundedLT
  exact Module.length_ne_top

end AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The separatedness instance used in this module. -/
local instance cyclesFinitePushforwardLengthDescentSeparated
    : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- The actual finite image-product section map supplies the coefficient action. -/
local instance remainingLengthCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.leftIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original supported-Tor remaining Koszul complex at one full-fiber point,
with the one common middle list transported by its actual stalk equality. -/
abbrev firstStageSourceRemainingKoszul
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :=
  _root_.ChainComplex.Koszul.coefficientComplex (F.firstStageSupportedStalkTor G H x.1 n)
    ((F.leftFiberMiddleList G H (V.2.fromSpec p) s x).map
      ((F.leftSupportMiddlePair G H).stalkMap x.1).hom)

variable (q : MaximalSpectrum
  (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
    Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p))

/-- Actual localized coefficient homology uses the canonical localization ring. -/
local instance remainingLengthLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- The localization algebra map uses the same canonical semiring structure. -/
local instance remainingLengthLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

/-- Flat maximal localization, the constructed common-list chain map and the
actual source structure-stalk equivalence identify every genuine homology length. -/
theorem firstStageWholeRemainingLocalizedHomology_length
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n r : ℕ) :
    Module.length (Localization.AtPrime q.asIdeal)
      ((ModuleCat.extendScalars (S := Localization.AtPrime q.asIdeal) (algebraMap
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
          Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p)
        (Localization.AtPrime q.asIdeal))).obj
          ((F.firstStageWholeRemainingKoszul G H V p s n).homology r)) =
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk
      (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q).1)
      ((F.firstStageSourceRemainingKoszul G H V p s
        (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q) n).homology r) := by
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
    Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p
  let C := F.firstStageWholeRemainingKoszul G H V p s n
  let D := F.firstStageSourceRemainingKoszul G H V p s
    (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q) n
  let e := originalSourceLocalizationIso (F.leftIntermediateImageMap G H) V.2 p q
  let φ := e.hom.hom
  exact (finiteAlgebraLocalizedHomologyIso T C q r).symm.toLinearEquiv.length_eq.trans
    (((HomologicalComplex.homologyFunctor _ _ r).mapIso
      (F.firstStageWholeRemainingLocalizedIso G H V p q s n)).toLinearEquiv.length_eq.trans
      (((D.sc r).mapHomologyIso (ModuleCat.restrictScalars φ)).toLinearEquiv.length_eq.trans
        (_root_.ModuleCat.length_restrictScalars_of_surjective φ
          e.commRingCatIsoToRingEquiv.surjective _)))

/-- Finite lengths on the genuine full source fiber descend to each actual whole
remaining-Koszul homology module. The geometric local-length proof is separate. -/
theorem firstStageWholeRemainingHomology_length_ne_top
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n r : ℕ)
    (hsource : ∀ x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = V.2.fromSpec p},
      Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk x.1)
        ((F.firstStageSourceRemainingKoszul G H V p s x n).homology r) ≠ ⊤) :
    Module.length
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
        Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p)
      ((F.firstStageWholeRemainingKoszul G H V p s n).homology r) ≠ ⊤ := by
  have := coordinateFinite (F.leftIntermediateImageMap G H) V.2
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
    Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p
  have : Finite (MaximalSpectrum T) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal) T
  apply length_ne_top_of_maximal T
    ((F.firstStageWholeRemainingKoszul G H V p s n).homology r)
  intro q
  rw [F.firstStageWholeRemainingLocalizedHomology_length G H V p q s n r]
  exact hsource (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q)

/-- Genuine source finite homology proves finite homology of the actual whole
remaining complex. Its inner degree support follows from the literal finite list. -/
theorem firstStageWholeRemaining_finiteHomology_of_source
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)
    (hsource : ∀ x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = V.2.fromSpec p},
      FiniteHomology (F.firstStageSourceRemainingKoszul G H V p s x n)) :
    FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n) := by
  apply FiniteLengthSupport.of_isZero_outside _
    (Finset.range ((F.firstStageWholeRemainingList G H V p s).length + 1))
  · intro r _
    exact F.firstStageWholeRemainingHomology_length_ne_top G H V p s n r
      (fun x => (hsource x).finite_length r)
  · intro r hr
    exact (HomologicalComplex.ExactAt.of_isZero
      (_root_.ChainComplex.Koszul.coefficient_isZero_X (F.firstStageWholeLocalizedCoefficient G H V
          p n)
        (F.firstStageWholeRemainingList G H V p s) r (by
          simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hr))).isZero_homology

end Motivic.FiniteCorrespondenceGenerator
