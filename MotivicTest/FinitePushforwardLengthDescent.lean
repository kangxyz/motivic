/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorRemainingLength
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian
public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyPlacement

/-!
# Actual whole-coefficient finite-length descent consumers

The contraction regression uses the genuine constructed Tor coefficient and
actual common-list scalar maps. A unit equation contracts every original source
complex, proving the local finite-homology witnesses used by the whole descent.
The geometric remaining-diagonal application is a separate consumer.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FinitePushforwardLengthDescent
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

omit [S.IsSeparated] [IsSeparated f] [IsSeparated h] [IsSeparated i] in
/-- The literal source list carrying one remains one through both actual stalk maps,
so the genuine supported Tor coefficient complex has a constructed contraction. -/
theorem actualUnitSource_finiteHomology
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p}) (n : ℕ) :
    FiniteHomology (F.firstStageSourceRemainingKoszul G H V p [1] x n) := by
  simp only [FiniteCorrespondenceGenerator.firstStageSourceRemainingKoszul,
    FiniteCorrespondenceGenerator.leftFiberMiddleList, List.map_cons, List.map_nil, map_one]
  exact _root_.ChainComplex.Koszul.finiteHomology_of_identity_homotopy _
    (_root_.ChainComplex.Koszul.singleUnitTensorHomotopy
      ((ChainComplex.single₀ (ModuleCat _)).obj (F.firstStageSupportedStalkTor G H x.1 n)))

/-- Actual whole remaining homology is finite by descent from the constructed source
contractions. No whole finite homology, Noetherianity or finite-length term premise is given. -/
theorem actualUnitWhole_finiteHomology (n : ℕ) :
    FiniteHomology (F.firstStageWholeRemainingKoszul G H V p [1] n) :=
  F.firstStageWholeRemaining_finiteHomology_of_source G H V p [1] n
    (fun x => actualUnitSource_finiteHomology F G H V p x n)

section Smooth

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

/-- Over every field, an actual generic final image-incidence point supplies a
chart and one regular diagonal list with finite whole homology in every Tor degree. -/
theorem actualSmoothWholeRemaining_chart
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H)) :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V)),
      V.2.fromSpec p = F.leftImageIncidenceInclusion G H y ∧
      ∃ s : List ((CategoryTheory.Limits.pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))),
        RingTheory.Sequence.IsRegular
          ((CategoryTheory.Limits.pullback Z.hom Z.hom).presheaf.stalk
            (F.leftImageMiddlePair G H (V.2.fromSpec p))) s ∧
        (CategoryTheory.Limits.pullback.diagonal Z.hom).ker.stalk
          (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s ∧
        ∀ n, FiniteHomology
          (F.firstStageWholeRemainingKoszul (S := Spec (.of K)) G H V p s n) :=
  F.exists_firstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy

/-- The same actual chart and list have finite whole remaining homology and a
geometrically derived uniform outer bound on the original localized Tor coefficient. -/
theorem actualSmoothWholeRemaining_finiteBounded
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H)) :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V)),
      V.2.fromSpec p = F.leftImageIncidenceInclusion G H y ∧
      ∃ s : List ((CategoryTheory.Limits.pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))),
        (∀ n, FiniteHomology
          (F.firstStageWholeRemainingKoszul (S := Spec (.of K)) G H V p s n)) ∧
        ∃ b : ℕ, ∀ n, b ≤ n →
          Subsingleton
            (F.firstStageWholeLocalizedCoefficient (S := Spec (.of K)) G H V p n) := by
  obtain ⟨V, p, hp, s, _, _, hfin⟩ := actualSmoothWholeRemaining_chart K X Y Z W F G H y hy
  exact ⟨V, p, hp, s, hfin,
    F.firstStageWholeLocalized_exists_bound (S := Spec (.of K)) G H V p⟩

end Smooth

end Motivic.MotivicTest.FinitePushforwardLengthDescent
